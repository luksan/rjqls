use std::io::stdin;
use std::iter;
use std::path::PathBuf;

use anyhow::{Context, Result};
use bpaf::{Bpaf, Parser};
use tracing::trace;
use tracing_subscriber::EnvFilter;

use rjqls::interpreter::AstInterpreter;
use rjqls::value::{ArcValue, JsonValue, Value};

#[derive(Bpaf, Clone, Debug)]
struct CommonOpts {
    #[bpaf(external, many)]
    arg: Vec<Arg>,

    /// By default, jq pretty-prints JSON output. Using this option will result in more compact
    /// output by instead putting each JSON object on a single line.
    #[bpaf(short('c'), long)]
    compact_output: bool,

    /// Don't read any input at all. Instead, the filter is run once using null as the input.
    /// This is useful when using jq as a simple calculator or to construct JSON data from scratch.
    #[bpaf(short('n'), long)]
    null_input: bool,

    /// Don't parse the input as JSON. Instead, each line of text is passed to the filter as a string.
    /// If combined with --slurp, then the entire input is passed to the filter as a single long string.
    #[bpaf(short('R'), long)]
    raw_input: bool,

    /// With this option, if the filter's result is a string then it will be written directly to
    /// standard output rather than being formatted as a JSON string with quotes.
    /// This can be useful for making jq filters talk to non-JSON-based systems.
    #[bpaf(short('r'), long)]
    raw_output: bool,

    /// Instead of running the filter for each JSON object in the input, read the entire input stream
    /// into a large array and run the filter just once.
    #[bpaf(short('s'), long)]
    slurp: bool,
}

#[derive(Debug, Clone, Bpaf)]
#[bpaf(adjacent)]
struct Arg {
    /// This option passes a value to the jq program as a predefined variable.
    /// If you run jq with --arg foo bar, then $foo is available in the program and has the value "bar".
    /// Note that value will be treated as a string, so --arg foo 123 will bind $foo to "123".
    ///
    /// Named arguments are also available to the jq program as $ARGS.named.
    #[bpaf(long)]
    #[allow(unused)]
    arg: (),
    #[bpaf(positional("name"))]
    name: String,
    #[bpaf(positional("value"))]
    value: String,
}

/// Reimplementation of jq in rust as a learning exercise.
#[derive(Debug, Clone, Bpaf)]
enum Opts {
    FilterFromFile {
        #[bpaf(external(common_opts))]
        common: CommonOpts,
        /// Read filter from the file rather than from a command line, like awk's -f option.
        /// You can also use '#' to make comments.
        #[bpaf(short('f'), long("from-file"), argument("filename"))]
        filter_file: PathBuf,
        /// Read input from the given files instead of stdin
        #[bpaf(positional("files"))]
        files: Vec<PathBuf>,
    },
    FilterFromCmdline {
        #[bpaf(external(common_opts))]
        common: CommonOpts,
        /// The jq program
        #[bpaf(positional("filter"))]
        filter: String,
        /// Read input from the given files instead of stdin
        #[bpaf(positional("files"))]
        files: Vec<PathBuf>,
    },
}

impl Opts {
    pub fn get_common_filter_and_files(self) -> Result<(CommonOpts, String, Vec<PathBuf>)> {
        let copts;
        let filter_str;
        let input_files;
        match self {
            Opts::FilterFromFile {
                common,
                filter_file,
                files,
            } => {
                copts = common;
                filter_str = std::fs::read_to_string(filter_file)?;
                input_files = files;
            }
            Opts::FilterFromCmdline {
                common,
                filter,
                files,
            } => {
                copts = common;
                filter_str = filter;
                input_files = files;
            }
        };
        Ok((copts, filter_str, input_files))
    }
}

fn read_value_from_stdin() -> Result<Option<Value>> {
    let mut input = String::new();
    let mut ret = Ok(None);
    loop {
        let res = stdin().read_line(&mut input)?;
        if res == 0 {
            return ret;
        }
        ret = serde_json::from_str(&input)
            .map(|json_val: JsonValue| Some(ArcValue::from(json_val)))
            .context("JSON value parse error");
        if ret.is_ok() {
            return ret;
        }
    }
}

fn eval_input_and_print(input: Value, interpreter: &mut AstInterpreter) -> Result<()> {
    for val in interpreter.eval_input(input)? {
        println!("{val}")
    }

    Ok(())
}

fn build_input_value_iterator(
    copts: &CommonOpts,
    input_files: Vec<PathBuf>,
) -> Box<dyn Iterator<Item = Result<Value>>> {
    if copts.null_input {
        return Box::new(iter::once(Ok(().into())));
    }

    if !input_files.is_empty() {
        let raw_values = input_files.into_iter().map(|file| {
            std::fs::read_to_string(file)
                .context("Couldn't read {file}")
                .map(|s| Value::from(s))
        });
        if !copts.raw_input {
            return Box::new(raw_values.map(|res| {
                res.and_then(|v| v.as_str().unwrap().parse().context("JSON parse error"))
            }));
        }
        return Box::new(raw_values);
    }

    let input_iter: Box<dyn Iterator<Item = Result<Value>>> = if !copts.raw_input {
        Box::new(
            iter::repeat_with(read_value_from_stdin)
                .take_while(|v| !matches!(v, Ok(None)))
                .map(|v| v.map(|opt| opt.unwrap())),
        )
    } else {
        // raw input
        Box::new(stdin().lines().map(|res| {
            res.map(|s| Value::from(s))
                .context("Failed to read from stdin")
        }))
    };
    input_iter
}

fn main() -> Result<()> {
    let opts = opts().run();
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .without_time()
        .init();
    trace!("Tracing is working.");

    let (copts, filter_str, input_files) = opts.get_common_filter_and_files()?;
    let mut prog = AstInterpreter::new(&filter_str)?;
    let mut inputs = build_input_value_iterator(&copts, input_files);

    for Arg { name, value, .. } in copts.arg {
        prog.set_variable(name, Value::from(value))
    }

    if copts.slurp {
        let input = if !copts.raw_input {
            let inputs: Result<Vec<_>> = inputs.collect();
            Value::from(inputs?)
        } else {
            let mut inputs: String = inputs.try_fold(String::new(), |mut acc, n| {
                acc.push_str(n?.as_str().unwrap());
                acc.push('\n');
                Ok::<_, anyhow::Error>(acc)
            })?;
            inputs.pop();
            Value::from(inputs)
        };
        eval_input_and_print(input, &mut prog)?;
    } else {
        for inp in inputs {
            eval_input_and_print(inp?, &mut prog)?;
        }
    }
    Ok(())
}
