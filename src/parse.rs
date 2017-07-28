use std::str;
use std::str::FromStr;
use nom::{is_alphabetic, is_alphanumeric, digit, hex_u32};

pub type Identifier = String;

#[derive(Debug, PartialEq, Eq)]
pub struct QualifiedName {
    structure: Identifier,
    field: Identifier,
}

// The TLS presentation language has two built-in types, `opaque` and `uint8`.
// These types are the same on the wire (octets), but numbers are built from
// arrays of `uint8` whereas uninterpreted octets are built from arrays of
// `opaque`.
//
// Fixed- and variable-length arrays, enumerated values, structures, and
// variants are (recursively) built from simpler types.

#[derive(Debug, PartialEq, Eq)]
pub enum Constant {
    Literal(u32),
    Named(Identifier),
    Qualified(QualifiedName),
}

// impl Constant {
//     pub fn is_literal(&self) -> bool {
//         match *self {
//             Constant::Literal(_) => true,
//             _                    => false,
//         }
//     }
//     pub fn is_named(&self) -> bool { !self.is_literal() }
// }

#[derive(Debug, PartialEq, Eq)]
pub struct Range {
    lower: u32,
    upper: u32,
}

#[derive(Debug, PartialEq, Eq)]
pub enum EnumValue {
    Literal(u32),
    Range(Range),
}


#[derive(Debug, PartialEq, Eq)]
pub enum FieldType {
    ScalarType,
    ConstantType(Constant),
    FixedVectorType(Constant),
    VariableVectorType(Range),
}

#[derive(Debug, PartialEq, Eq)]
pub struct FieldDecl {
    base: Identifier, // Base type.
    name: Identifier, // Field name.
    typ:  FieldType,  // Type of field.
}

#[derive(Debug, PartialEq, Eq)]
pub struct VariantDecl {
    qname: QualifiedName,
    cases: Vec<(Identifier, FieldDecl)>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeDeclType {
    Alias {
        base: Identifier,
    },
    FixedVector {
        base: Identifier,
        size: Constant,
    },
    VariableVector {
        base: Identifier,
        range: Range,
    },
    Enum {
        elements: Vec<(Identifier, EnumValue)>,
        max: Option<u32>,
    },
    Struct {
        fields: Vec<FieldDecl>,
        variant: Option<VariantDecl>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeDecl {
    name: Identifier,
    typ: TypeDeclType,
}

// The TLS 1.3 presentation language is described in Section 3 of
// draft-ietf-tls-tls13-21. As there is no formal specification, each part of
// the parser will explicitly indicate the text from the draft it is based on or
// will document the requirements I have inferred.

// Identifiers. Identifiers are not specified in the standard. Let's assume
// identifiers start with a letter and consist of letters and numbers.

fn is_identifier(c: u8) -> bool {
    is_alphanumeric(c) || c == b'_'
}

named!(identifier<Identifier>,
    map_res!(
        map_res!(verify!(take_while1!(is_identifier),
                         |s: &[u8]| is_alphabetic(s[0])),
                 str::from_utf8),
        String::from_str));

named!(qualified_name<QualifiedName>,
       do_parse!(structure: identifier >>
                 char!('.')            >>
                 field: identifier     >>
                 (QualifiedName {
                     structure: structure,
                     field: field,
                 })));

// Number expressions. These aren't specified in the standard.
// Recognize decimal and hexadecimal numbers.
named!(number<u32>,
    alt!(preceded!(complete!(tag!("0x")), hex_u32) |
         map_res!(map_res!(digit, str::from_utf8), str::parse::<u32>)));
// Recognize numbers and very limited expressions of the form
// 2^number[[-number]]
// This could easily be more expressive.
named!(num_expr<u32>,
    alt!(do_parse!(
                 tag!("2^") >>
            exp: number >>
            sub: opt!(preceded!(char!('-'), number)) >>
            ((1 << exp) - sub.unwrap_or(0))) |
         number));

named!(constant<Constant>,
    alt!(map!(qualified_name, Constant::Qualified) |
         map!(identifier,     Constant::Named) |
         map!(num_expr,       Constant::Literal)));

// Range expressions. These aren't specified in the standard but lower..upper is
// appears several times.
named!(range<Range>,
       do_parse!(lower: num_expr >>
                 tag!("..")      >>
                 upper: num_expr >>
                 (Range {lower: lower, upper: upper })));

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

// 3.2 Type aliases.
named!(alias_decl<TypeDecl>,
    sp!(do_parse!(
        base: identifier >>
        name: identifier >>
              char!(';') >>
        (TypeDecl {
            name: name,
            typ: TypeDeclType::Alias {
                base: base,
            },
        }))));

// 3.3. Vectors
//
// > The syntax for specifying a new type, T', that is a fixed-length vector of
// > type T is
// >     T T'[n];
named!(fixed_vector_decl<TypeDecl>,
       sp!(do_parse!(base: identifier >>
                     name: identifier >>
                           char!('[') >>
                     size: constant   >>
                           char!(']') >>
                           char!(';') >>
                     (TypeDecl {
                         name: name,
                         typ : TypeDeclType::FixedVector {
                             base: base,
                             size: size,
                         },
                     }))));

// > Variable-length vectors are defined by specifying a subrange of legal 
// > lengths, inclusively, using the notation <floor..ceiling>.
// >     T T'<floor..ceiling>
named!(variable_vector_decl<TypeDecl>,
       sp!(do_parse!(base: identifier >>
                     new:  identifier >>
                           char!('<') >>
                     rng:  range      >>
                           char!('>') >>
                           char!(';') >>
                     (TypeDecl {
                         name: new,
                         typ : TypeDeclType::VariableVector {
                             base: base,
                             range: rng,
                         },
                     }))));

// 3.5. Enumerateds.
// > enum { e1(v1), e2(v2), ... , en(vn) [[, (vm)]] } Te;
named!(enum_element<(Identifier, EnumValue)>,
    do_parse!(
        name:  identifier >>
               char!('(') >>
        lower: num_expr   >>
        upper: opt!(preceded!(tag!(".."), num_expr)) >>
               char!(')') >>
        ((name, upper.map_or(EnumValue::Literal(lower),
                             |u| EnumValue::Range(Range {lower: lower, upper:u}))))));

named!(enum_decl<TypeDecl>,
       sp!(do_parse!(tag!("enum")     >>
                     char!('{')       >>
                     elements: separated_nonempty_list!(sp!(char!(',')), enum_element) >>
                     max: opt!(preceded!(sp!(char!(',')),
                                         delimited!(char!('('), num_expr, char!(')')))) >>
                     char!('}')       >>
                     name: identifier >>
                     char!(';')       >>
                     (TypeDecl {
                        name: name,
                        typ: TypeDeclType::Enum {
                            elements: elements,
                            max: max,
                        },
                     }))));

// 3.6. Constructed Types

named!(scalar_type<FieldType>,
       sp!(do_parse!(char!(';') >>
                     (FieldType::ScalarType))));

named!(constant_type<FieldType>,
       sp!(do_parse!(char!('=') >>
                     num: constant >>
                     char!(';') >>
                     (FieldType::ConstantType(num)))));

named!(fixed_vector_type<FieldType>,
       sp!(do_parse!(char!('[')     >>
                     size: constant >>
                     char!(']')     >>
                     char!(';')     >>
                     (FieldType::FixedVectorType(size)))));

named!(variable_vector_type<FieldType>,
       sp!(do_parse!(char!('<') >>
                     rng: range >>
                     char!('>') >>
                     char!(';') >>
                     (FieldType::VariableVectorType(rng)))));

named!(field_decl<FieldDecl>,
       sp!(do_parse!(base: identifier >>
                     name: identifier >>
                     typ: alt!(scalar_type |
                               constant_type |
                               fixed_vector_type |
                               variable_vector_type) >>
                     (FieldDecl {
                        base: base,
                        name: name,
                        typ: typ,
                     }))));

named!(case_stmt<(Identifier, FieldDecl)>,
       sp!(do_parse!(tag!("case")      >>
                     arm: identifier   >>
                     char!(':')        >>
                     field: alt!(map!(sp!(terminated!(identifier, char!(';'))),
                                      |base| FieldDecl {
                                          base: base,
                                          name: "".to_string(),
                                          typ: FieldType::ScalarType,
                                      }) |
                                 field_decl) >>
                     ((arm, field)))));

named!(select_stmt<VariantDecl>,
       sp!(do_parse!(tag!("select")           >>
                     char!('(')               >>
                     qname: qualified_name    >>
                     char!(')')               >>
                     char!('{')               >>
                     cases: many1!(case_stmt) >>
                     char!('}')               >>
                     char!(';')               >>
                     (VariantDecl {
                         qname: qname,
                         cases: cases,
                     }))));

named!(struct_decl<TypeDecl>,
       sp!(do_parse!(tag!("struct")             >>
                     char!('{')                 >>
                     fields: many0!(field_decl) >>
                     variant: opt!(select_stmt) >>
                     char!('}')                 >>
                     name: identifier           >>
                     char!(';')                 >>
                     (TypeDecl {
                        name: name,
                        typ: TypeDeclType::Struct {
                            fields: fields,
                            variant: variant,
                        },
                     }))));

named!(type_decl<TypeDecl>,
    sp!(alt!(enum_decl |
             struct_decl |
             fixed_vector_decl |
             variable_vector_decl |
             alias_decl)));

named!(type_decls<Vec<TypeDecl>>, sp!(many1!(type_decl)));

pub fn parse_types(input: &str) -> Result<Vec<TypeDecl>, String> {
    use nom::IResult;
    match complete!(input.as_bytes(), sp!(type_decls)) {
        IResult::Done(rest, types) => {
            if rest != &[][..] {
                let num = types.len();
                let parsed_types = types.into_iter()
                    .map(|decl| decl.name)
                    .collect::<Vec<String>>()
                    .join(", ");
                let msg = format!("Successfully parsed {} types (", num).to_string() +
                    &parsed_types + ") but could not parse\n" +
                    str::from_utf8(rest).unwrap();
                Err(msg)
            } else {
                Ok(types)
            }
        },
        IResult::Error(err)        => Err(format!("{}", err)),
        IResult::Incomplete(_)     => panic!("Incomplete?!?"),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use nom::IResult;

    macro_rules! assert_parse {
        ($res: expr, $expected: expr) => {
            match $res {
                IResult::Done(i, actual) => assert_eq!((str::from_utf8(i).unwrap(),actual), ("", $expected)),
                IResult::Error(e)        => panic!(format!("{}", e)),
                IResult::Incomplete(n)   => panic!(format!("{:?}", n)),
            }
        };
    }

    #[test]
    fn check_identifier() {
        assert_parse!(identifier(b"A"),            "A".to_string());
        assert_parse!(identifier(b"foo"),          "foo".to_string());
        assert_parse!(identifier(b"Num32"),        "Num32".to_string());
        assert_parse!(identifier(b"foo_RESERVED"), "foo_RESERVED".to_string());
        
        // Invalid identifiers.
        assert!(identifier(b"23foo").is_err());
    }
    
    #[test]
    fn check_num_expr() {
        assert_parse!(num_expr(b"0xa1F3"), 0xa1f3);
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
    fn check_alias_decl() {
        let protocol_version = TypeDecl {
            name: "ProtocolVersion".to_string(),
            typ: TypeDeclType::Alias {
                base: "uint16".to_string(),
            },
        };
        assert_parse!(type_decl(b"uint16 ProtocolVersion;"), protocol_version);
    }
    
    #[test]
    fn check_fixed_vector_decl() {
        let uint16 = TypeDecl {
            name: "uint16".to_string(),
            typ: TypeDeclType::FixedVector {
                base: "uint8".to_string(),
                size: Constant::Literal(2),
            },
        };
        assert_parse!(type_decl(b"uint8 uint16[2];"), uint16);
    }

    #[test]
    fn check_variable_vec_decl() {
        let mandatory = TypeDecl {
            name: "mandatory".to_string(),
            typ: TypeDeclType::VariableVector {
                base: "opaque".to_string(),
                range: Range { lower: 300, upper: 400 },
            },
        };
        assert_parse!(type_decl(b"opaque mandatory<300..400>;"), mandatory);
        let longer = TypeDecl {
            name: "longer".to_string(),
            typ: TypeDeclType::VariableVector {
                base: "uint16".to_string(),
                range: Range { lower: 0, upper: 800 },
            },
        };
        assert_parse!(type_decl(b"uint16 longer<0..800>;"), longer);
    }

    #[test]
    fn check_enum_decl() {
        let color = TypeDecl {
            name: "Color".to_string(),
            typ: TypeDeclType::Enum {
                elements: vec![("red".to_string(),   EnumValue::Literal(3)),
                               ("blue".to_string(),  EnumValue::Literal(5)),
                               ("white".to_string(), EnumValue::Literal(7))],
                max: None,
            },
        };
        assert_parse!(type_decl(b" enum { red(3), blue(5), white(7) } Color;"), color);
        let taste = TypeDecl {
            name: "Taste".to_string(),
            typ: TypeDeclType::Enum {
                elements: vec![("sweet".to_string(),  EnumValue::Literal(1)),
                               ("sour".to_string(),   EnumValue::Literal(2)),
                               ("bitter".to_string(), EnumValue::Literal(4))],
                max: Some(32000),
            },
        };
        assert_parse!(type_decl(b"enum { sweet(1), sour(2), bitter(4), (32000) } Taste;"), taste);
        let reserved = TypeDecl {
            name: "Reserved".to_string(),
            typ: TypeDeclType::Enum {
                elements: vec![("foo".to_string(), EnumValue::Literal(1)),
                               ("reserved".to_string(), EnumValue::Range(Range { lower: 300, upper: 400 }))],
                max: Some(65535),
            },
        };
        assert_parse!(type_decl(b"enum { foo(1), reserved(300..400), (65535) } Reserved;"), reserved);
    }

    #[test]
    fn check_parse() {
    }
}

// vim: tw=80:
