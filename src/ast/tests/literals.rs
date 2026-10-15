use crate::ast::{Expression, ExpressionInner, SingleExpressionInner};
use crate::parse::{self, ParseFromStr};
use crate::types::UIntType;
use crate::value::{UIntValue, Value};

#[test]
fn analyzed_numeric_literals_accept_digit_separators() {
    let cases = [
        ("1_337", UIntType::U16, Value::from(UIntValue::U16(1_337))),
        (
            "0b1010_0101",
            UIntType::U8,
            Value::from(UIntValue::U8(0b1010_0101)),
        ),
        (
            "0xDE_AD_BE_EF",
            UIntType::U32,
            Value::from(UIntValue::U32(0xdead_beef)),
        ),
    ];

    for (source, integer_type, expected) in cases {
        let parsed = parse::Expression::parse_from_str(source).expect("literal parses");
        let analyzed =
            Expression::analyze_const(&parsed, &integer_type.into()).expect("literal analyzes");

        let ExpressionInner::Single(single) = analyzed.inner() else {
            panic!("expected a single expression")
        };
        let SingleExpressionInner::Constant(value) = single.inner() else {
            panic!("expected a constant expression")
        };

        assert_eq!(value, &expected, "unexpected value for {source:?}");
        assert_eq!(single.span().to_slice(source), Some(source));
    }
}
