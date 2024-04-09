use rjqls::interpreter::AstInterpreter;
use rjqls::value::Value;

#[test]
fn test_include_ok() {
    let mut int = AstInterpreter::new(r#"include "tests/test_include"; func_b"#).unwrap();
    let one = int.eval_input(Value::Null).unwrap();
    assert_eq!(one[0].as_bigint(), Some(2))
}

#[test]
fn test_include_bad() {
    let err = AstInterpreter::new(r#"include "tests/bad_include"; ."#).unwrap_err();
    assert!(err
        .to_string()
        .contains("library should only have function definitions"))
}
