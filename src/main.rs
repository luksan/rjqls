use std::io::stdin;
use std::iter;
use std::path::PathBuf;

use anyhow::{Context, Result};
use bpaf::{Bpaf, Parser};
use serde_json::Value;
use tracing::Level;

use rjqls::interpreter::AstInterpreter;

#[derive(Bpaf, Clone, Debug)]
struct CommonOpts {
    /// Don't read any input at all. Instead, the filter is run once using null as the input.
    /// This is useful when using jq as a simple calculator or to construct JSON data from scratch.
    #[bpaf(short('n'), long)]
    null_input: bool,

    /// Don't parse the input as JSON. Instead, each line of text is passed to the filter as a string.
    /// If combined with --slurp, then the entire input is passed to the filter as a single long string.
    #[bpaf(short('R'), long)]
    raw_input: bool,

    /// Instead of running the filter for each JSON object in the input, read the entire input stream
    /// into a large array and run the filter just once.
    #[bpaf(short('s'), long)]
    slurp: bool,
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
            .map(Some)
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
        return Box::new(iter::once(Ok(Value::Null)));
    }

    if !input_files.is_empty() {
        let raw_values = input_files.into_iter().map(|file| {
            std::fs::read_to_string(file)
                .context("Couldn't read {file}")
                .map(Value::String)
        });
        if !copts.raw_input {
            return Box::new(raw_values.map(|res| {
                res.and_then(|v| {
                    let Value::String(s) = v else { unreachable!() };
                    serde_json::from_str(&s).context("JSON parse error")
                })
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
        Box::new(
            stdin()
                .lines()
                .map(|res| res.map(Value::String).context("Failed to read from stdin")),
        )
    };
    input_iter
}

fn main() -> Result<()> {
    let opts = opts().run();
    tracing_subscriber::fmt()
        .with_max_level(Level::TRACE)
        .without_time()
        .init();

    let (copts, filter_str, input_files) = opts.get_common_filter_and_files()?;
    let mut prog = AstInterpreter::new(&filter_str)?;
    let inputs = build_input_value_iterator(&copts, input_files);

    if copts.slurp {
        let input = if !copts.raw_input {
            let inputs: Result<Vec<_>> = inputs.collect();
            Value::Array(inputs?)
        } else {
            let inputs: Vec<String> = inputs
                .map(|res| {
                    res.map(|v| {
                        let Value::String(s) = v else { unreachable!() };
                        s
                    })
                })
                .collect::<Result<_>>()?;
            Value::String(inputs.join("\n"))
        };
        eval_input_and_print(input, &mut prog)?;
    } else {
        for inp in inputs {
            eval_input_and_print(inp?, &mut prog)?;
        }
    }
    Ok(())
}
