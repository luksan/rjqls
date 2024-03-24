use anyhow::bail;
use onig::{Regex, RegexOptions, Syntax};

use super::*;

fn parse_modifiers(mods: &Value) -> Result<(bool, RegexOptions)> {
    let mods = mods
        .as_str()
        .with_context(|| format!("{mods} is not a string"))?;
    let mut ret = RegexOptions::REGEX_OPTION_CAPTURE_GROUP;
    let mut global = false;
    for m in mods.chars() {
        match m {
            'g' => global = true,
            'i' => ret |= RegexOptions::REGEX_OPTION_IGNORECASE,
            'x' => ret |= RegexOptions::REGEX_OPTION_EXTEND,
            'm' => ret |= RegexOptions::REGEX_OPTION_MULTILINE,
            's' => ret |= RegexOptions::REGEX_OPTION_SINGLELINE,
            'p' => {
                ret |= RegexOptions::REGEX_OPTION_MULTILINE | RegexOptions::REGEX_OPTION_SINGLELINE
            }
            'l' => ret |= RegexOptions::REGEX_OPTION_FIND_LONGEST,
            'n' => ret |= RegexOptions::REGEX_OPTION_FIND_NOT_EMPTY,
            _ => bail!("{mods} is not a valid modifier string"),
        }
    }
    Ok((global, ret))
}

pub(super) fn f_match(
    input: &Value,
    regex: &Value,
    modifiers: &Value,
    testmode: &Value,
) -> Result<Value> {
    let testmode = testmode.is_truthy();
    let input = input
        .as_str()
        .with_context(|| format!("{input} cannot be matched, as it is not a string"))?;
    let regex = regex
        .as_str()
        .with_context(|| format!("{regex} is not a string"))?;
    let (global, regex_opts) = parse_modifiers(modifiers)?;
    let re = Regex::with_options(regex, regex_opts, Syntax::perl_ng())
        .context("Invalid regular expression")?;

    let mut caps_iter: &mut dyn Iterator<Item = _> = &mut re.captures_iter(input);
    if testmode {
        return Ok(Value::Bool(caps_iter.next().is_some()));
    }
    let mut take_one;
    if !global {
        take_one = caps_iter.take(1);
        caps_iter = &mut take_one;
    }

    let caps: Vec<_> = caps_iter
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
    Ok(Value::from(caps))
}

#[cfg(test)]
mod regex_tests {
    use super::*;

    #[test]
    fn test_regex_match() {
        let regex = Value::from(r#"c(d)(?<x>e)"#);
        let input: Value = "abcde".into();
        f_match(&input, &regex, &Value::from(""), &Value::from(false)).unwrap();
    }
}
