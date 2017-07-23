#[macro_use]
extern crate nom;

use nom::{alpha, alphanumeric, digit};
use std::str;

// The TLS 1.3 presentation language is described in Section 3 of
// draft-ietf-tls-tls13-21. As there is no formal specification, each part of
// the parser will explicitly indicate the text from the draft it is based on or
// will document the requirements I have inferred.

// Identifiers. Identifiers are not specified in the standard. Let's assume
// identifiers start with a letter and consist of letters and numbers.
named!(identifier<&str>,
       map_res!(recognize!(do_parse!(alpha >> many0!(alphanumeric) >> ())),
                str::from_utf8));

// Number expressions. These aren't specified in the standard.
named!(num_expr<u32>,
       map_res!(map_res!(recognize!(many1!(digit)),
                         str::from_utf8),
                str::parse::<u32>));

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

// Vectors. Section 3.3
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
       sp!(do_parse!(base_ty: identifier >>
                     new_ty: identifier  >>
                     char!('<')          >>
                     floor: num_expr     >>
                     tag!("..")          >>
                     ceiling: num_expr   >>
                     char!('>')          >>
                     (VariableVectorType::new(new_ty, base_ty, floor, ceiling)))));

// Enumerateds. Section 3.5.
// > enum { e1(v1), e2(v2), ... , en(vn) [[, (n)]] } Te;


#[cfg(test)]
mod test {
    use ::*;
    use nom::IResult::Done;

    #[test]
    fn check_identifier() {
        let empty = &b""[..];
        assert_eq!(identifier(b"A"),     Done(empty, "A"));
        assert_eq!(identifier(b"foo"),   Done(empty, "foo"));
        assert_eq!(identifier(b"Num32"), Done(empty, "Num32"));
        
        // Invalid identifiers.
        assert!(identifier(b"23foo").is_err());
    }
    
    #[test]
    fn check_num_expr() {
        let empty = &b""[..];
        assert_eq!(num_expr(b"12345"), Done(empty, 12345));
        assert_eq!(num_expr(b"0"),     Done(empty, 0));
    
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
        let empty = &b""[..];
        let uint16 = FixedVectorType::new("uint16", "uint8", 2);
        assert_eq!(fixed_vec_type(b"uint8 uint16[2]"), Done(empty, uint16));
    }
    
    #[test]
    fn check_variable_vec_type() {
        let empty = &b""[..];
        let mandatory = VariableVectorType::new("mandatory", "opaque", 300, 400);
        let longer = VariableVectorType::new("longer", "uint16", 0, 800);
        assert_eq!(variable_vec_type(b"opaque mandatory<300..400>"), Done(empty, mandatory));
        assert_eq!(variable_vec_type(b"uint16 longer<0..800>"), Done(empty, longer));
    }
}

fn main() {
    println!("Run `cargo test`");
}

// vim: tw=80:
