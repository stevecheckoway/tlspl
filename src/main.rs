#[macro_use]
extern crate nom;

use nom::{alphanumeric, digit};
use std::str;

// The TLS 1.3 presentation language is described in Section 3 of
// draft-ietf-tls-tls13-21. As there is no formal specification, each part of
// the parser will explicitly indicate the text from the draft it is based on or
// will document the requirements I have inferred.

// Identifiers. Identifiers are not specified in the standard. Let's assume
// identifiers start with a letter and consist of letters and numbers.

named!(identifier<&str>,
       map_res!(verify!(alphanumeric, |s: &[u8]| nom::is_alphabetic(s[0])),
                str::from_utf8));

// Number expressions. These aren't specified in the standard.
named!(num_expr<u32>,
       map_res!(map_res!(digit, str::from_utf8),
                str::parse::<u32>));

// Range expressions. These aren't specified in the standard but lower..upper is
// appears several times.
named!(range_expr<(u32, u32)>,
       do_parse!(lower: num_expr >>
                 tag!("..")      >>
                 upper: num_expr >>
                 (lower, upper)));

// Comments. Section 3.2.
// 
// > Comments begin with "/*" and end with "*/".
named!(comment,
       recognize!(do_parse!(tag!("/*") >> take_until_and_consume!("*/") >> ())));

// Make our own whitespace parser to consume spaces, tabs, carriage returns,
// newlines, and comments.
named!(pub space,
       recognize!(many1!(alt!(eat_separator!(&b" \t\r\n"[..]) | comment))));

#[macro_export]
macro_rules! sp (
    ($i:expr, $($args:tt)*) => (
        {
            sep!($i, space, $($args)*)
        }
    )
);

// 3.3. Vectors
//
// > The syntax for specifying a new type, T', that is a fixed-length vector of
// > type T is
// >     T T'[n];
// > Variable-length vectors are defined by specifying a subrange of legal 
// > lengths, inclusively, using the notation <floor..ceiling>.
// >     T T'<floor..ceiling>

#[derive(Eq, PartialEq, Debug)]
struct FixedVectorType {
    name: String,
    base: String,
    size: u32,
}

impl FixedVectorType {
    pub fn new(name: &str, base: &str, size: u32) -> FixedVectorType {
        FixedVectorType {
            name: name.to_string(),
            base: base.to_string(),
            size: size,
        }
    }
}

#[derive(Eq, PartialEq, Debug)]
struct VariableVectorType {
    name: String,
    base: String,
    floor: u32,
    ceiling: u32,
}

impl VariableVectorType {
    pub fn new(name: &str, base: &str, floor: u32, ceiling: u32) -> VariableVectorType {
        VariableVectorType {
            name: name.to_string(),
            base: base.to_string(),
            floor: floor,
            ceiling: ceiling,
        }
    }
}

named!(fixed_vec_type<FixedVectorType>,
       sp!(do_parse!(base_ty: identifier >>
                     new_ty: identifier  >>
                     char!('[')          >>
                     len: num_expr       >>
                     char!(']')          >>
                     (FixedVectorType::new(new_ty, base_ty, len)))));

named!(variable_vec_type<VariableVectorType>,
       sp!(do_parse!(base_ty: identifier       >>
                     new_ty: identifier        >>
                     char!('<')                >>
                     floor_ceiling: range_expr >>
                     char!('>')                >>
                     (VariableVectorType::new(new_ty, base_ty, floor_ceiling.0, floor_ceiling.1)))));

// 3.5. Enumerateds.
// > enum { e1(v1), e2(v2), ... , en(vn) [[, (n)]] } Te;

#[derive(Eq, PartialEq, Debug)]
struct EnumType {
    name: String,
    elements: Vec<(String, u32)>,
    max: Option<u32>,
}

impl EnumType {
    pub fn new(name: &str, elements: Vec<(&str, u32)>, max: Option<u32>) -> EnumType {
        EnumType {
            name: name.to_string(),
            elements: elements.iter().map(|&(e, v)| (e.to_string(), v)).collect(),
            max: max,
        }
    }
}

// XXX: This should support ranges too.
named!(enum_value<u32>,
       delimited!(char!('('), num_expr, char!(')')));

named!(enum_element<(&str, u32)>,
       do_parse!(element: identifier >>
                 value: enum_value   >>
                 (element, value)));

named!(enum_type<EnumType>,
       sp!(do_parse!(tag!("enum")          >>
                     char!('{')            >>
                     elements: separated_nonempty_list!(sp!(char!(',')), enum_element) >>
                     max: opt!(preceded!(sp!(char!(',')), enum_value)) >>
                     char!('}')            >>
                     name: identifier      >>
                     (EnumType::new(name, elements, max)))));

// 3.6. Constructed Types
// The basic structure type looks like this.
// >     struct {
// >         T1 f1;
// >         T2 f2;
// >         ...
// >         Tn fn;
// >     } [[T]];
//
// 3.7. Constants
// > Fields and variables may be assigned a fixed value using "=", as in:
// >
// >     struct {
// >         T1 f1 = 8;  /* T.f1 must always be 8 */
// >         T2 f2;
// >     } T;
//
// 3.8. Variants
//
// >     struct {
// >         T1 f1;
// >         T2 f2;
// >         ....
// >         Tn fn;
// >         select (E) {
// >             case e1: Te1;
// >             case e2: Te2;
// >             ....
// >             case en: Ten;
// >         } [[fv]];
// >     } [[Tv]];






#[cfg(test)]
mod test {
    use ::*;
    use nom::IResult;

    macro_rules! assert_parse {
        ($res: expr, $expected: expr) => {
            match $res {
                IResult::Done(i, actual) => assert_eq!((i,actual), (&[][..], $expected)),
                IResult::Error(e)        => panic!(format!("{}", e)),
                IResult::Incomplete(n)   => panic!(format!("{:?}", n)),
            }
        };
    }

    #[test]
    fn check_identifier() {
        assert_parse!(identifier(b"A"),     "A");
        assert_parse!(identifier(b"foo"),   "foo");
        assert_parse!(identifier(b"Num32"), "Num32");
        
        // Invalid identifiers.
        assert!(identifier(b"23foo").is_err());
    }
    
    #[test]
    fn check_num_expr() {
        assert_parse!(num_expr(b"12345"), 12345);
        assert_parse!(num_expr(b"0"),     0);
    
        assert!(num_expr(b"a23").is_err());
    }
    
    #[test]
    fn check_comment() {
        assert!(comment(b"/* foo * bar */").is_done());
        assert!(comment(b"/**/").is_done());
    
        assert!(!comment(b"/*/").is_done());
    }
    
    #[test]
    fn check_fixed_vec_type() {
        let uint16 = FixedVectorType::new("uint16", "uint8", 2);
        assert_parse!(fixed_vec_type(b"uint8 uint16[2]"), uint16);
    }
    
    #[test]
    fn check_variable_vec_type() {
        let mandatory = VariableVectorType::new("mandatory", "opaque", 300, 400);
        let longer = VariableVectorType::new("longer", "uint16", 0, 800);
        assert_parse!(variable_vec_type(b"opaque mandatory<300..400>"), mandatory);
        assert_parse!(variable_vec_type(b"uint16 longer<0..800>"), longer);
    }

    #[test]
    fn check_enum_type() {
        let color_res = enum_type(b"enum { red(3), blue(5), white(7) } Color");
        let color = EnumType::new("Color", vec![("red", 3), ("blue", 5), ("white", 7)], None);
        assert_parse!(color_res, color);
        let taste_res = enum_type(b"enum { sweet(1), sour(2), bitter(4), (32000) } Taste");
        let taste = EnumType::new("Taste", vec![("sweet", 1), ("sour", 2), ("bitter", 4)], Some(32000));
        assert_parse!(taste_res, taste);
    }
}

fn main() {
    println!("Run `cargo test`");
}

// vim: tw=80:
