use onig::{Regex, RegexOptions, Syntax};

use super::*;

impl<'e> ExprEval<'e> {
    pub fn match_1(&self, args: &'e [Expr]) -> Result<Generator<'e>> {
        let regex = args[0]
            .accept(self)?
            .next()
            .context("match argument must be a string")??;
        let regex = regex
            .as_array()
            .and_then(|a| a.get(0))
            .unwrap_or(&regex)
            .as_str()
            .context("match argument must be a string")?;
        let input = self.input.as_str().with_context(|| {
            format!(
                "{} cannot be matched since it is not a string.",
                &self.input
            )
        })?;
        let regex_opts = RegexOptions::REGEX_OPTION_CAPTURE_GROUP;
        let re = Regex::with_options(regex, regex_opts, Syntax::perl_ng())
            .context("Invalid regular expression")?;

        let caps: Vec<Value> = re
            .captures_iter(input)
            .map(|cap| {
                let mut obj = Map::new();
                let mtch = cap.at(0).unwrap();
                obj.insert("offset".to_owned(), cap.offset().into());
                obj.insert("length".to_owned(), mtch.len().into());
                obj.insert("string".to_owned(), mtch.into());
                let mut subs: Vec<Value> = cap
                    .iter_pos()
                    .skip(1)
                    .map(|tuple_opt| {
                        let mut obj = Map::new();
                        if let Some((start, end)) = tuple_opt {
                            let a = start - cap.offset();
                            let b = end - cap.offset();
                            let txt = mtch[a..b].to_owned();
                            let len = txt.len().into();
                            obj.insert("offset".to_owned(), start.into());
                            obj.insert("string".to_owned(), txt.into());
                            obj.insert("length".to_owned(), len);
                        } else {
                            obj.insert("offset".to_owned(), Value::from(-1));
                            obj.insert("string".to_owned(), ().into());
                            obj.insert("length".to_owned(), 0.into());
                        }
                        obj.insert("name".to_owned(), ().into());
                        obj.into()
                    })
                    .collect();

                re.foreach_name(|name, pos| {
                    subs[pos[0] as usize - 1]
                        .as_mut_obj()
                        .unwrap()
                        .insert("name".to_owned(), name.into());
                    true
                });

                obj.insert("captures".to_owned(), subs.into());
                obj.into()
            })
            .collect();
        Ok(Generator::from_iter(caps.into_iter().map(|o| Ok(o))))
    }
}
