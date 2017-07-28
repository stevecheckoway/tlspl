use std::str;
use std::str::FromStr;
use nom::{is_alphabetic, is_alphanumeric, digit, hex_u32};

pub type Identifier = String;

#[derive(Debug, PartialEq, Eq)]
pub enum Name {
    Simple(Identifier),
    Qualified(Identifier, Identifier), // structure, field
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
    Named(Name),
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
    pub lower: u32,
    pub upper: u32,
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
    pub base: Identifier, // Base type.
    pub name: Identifier, // Field name.
    pub typ:  FieldType,  // Type of field.
}

#[derive(Debug, PartialEq, Eq)]
pub struct VariantDecl {
    pub selector: Name,
    pub cases: Vec<(Identifier, FieldDecl)>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum StructElement {
    Field(FieldDecl),
    Variant(VariantDecl),
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
        fields: Vec<StructElement>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeDecl {
    pub name: Identifier,
    pub typ: TypeDeclType,
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

named!(name<Name>,
    do_parse!(
        structure: identifier >>
        field:     opt!(preceded!(char!('.'), identifier)) >>
        (match field { None        => Name::Simple(structure),
                       Some(field) => Name::Qualified(structure, field) })));

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
    alt!(map!(name,     Constant::Named) |
         map!(num_expr, Constant::Literal)));

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
named!(comment_space,
    recognize!(
        preceded!(eat_separator!(&b" \t\r\n"[..]),
                  many0!(terminated!(comment, eat_separator!(&b" \t\r\n"[..]))))));

#[macro_export]
macro_rules! sp (
    ($i:expr, $($args:tt)*) => (
        {
            sep!($i, comment_space, $($args)*)
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
                     selector: name           >>
                     char!(')')               >>
                     char!('{')               >>
                     cases: many1!(case_stmt) >>
                     char!('}')               >>
                     char!(';')               >>
                     (VariantDecl {
                         selector: selector,
                         cases:    cases,
                     }))));

named!(struct_decl<TypeDecl>,
       sp!(do_parse!(tag!("struct")                  >>
                     char!('{')                      >>
                     fields: sp!(many0!(alt!(
                                map!(select_stmt, StructElement::Variant) |
                                map!(field_decl,  StructElement::Field)))) >>
                     char!('}')                      >>
                     name: identifier                >>
                     char!(';')                      >>
                     (TypeDecl {
                        name: name,
                        typ: TypeDeclType::Struct {
                            fields: fields,
                        },
                     }))));

named!(type_decl<TypeDecl>,
    sp!(alt!(enum_decl |
             struct_decl |
             fixed_vector_decl |
             variable_vector_decl |
             alias_decl)));

named!(type_decls<Vec<TypeDecl>>, sp!(many0!(type_decl)));

pub fn parse_types(input: &str) -> Result<(Vec<TypeDecl>, &str), String> {
    use nom::IResult;
    match complete!(input.as_bytes(), sp!(type_decls)) {
        IResult::Done(rest, types) => Ok((types, str::from_utf8(rest).unwrap())),
        IResult::Error(err)        => Err(format!("{}", err)),
        IResult::Incomplete(_)     => panic!("Incomplete?!?"),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use nom::{IResult, Err};
    //use std::error::Error;
    
    fn convert_vec<E>(v: Vec<Err<&[u8], E>>) -> Vec<Err<&str, E>> {
        v.into_iter()
            .map(convert_err)
            .collect()
    }

    fn convert_err<E>(err : Err<&[u8], E>) -> Err<&str, E> {
        match err {
            Err::Code(k) => Err::Code(k),
            Err::Node(k, v) => Err::Node(k, convert_vec(v)),
            Err::Position(k, p) => Err::Position(k, str::from_utf8(p).unwrap()),
            Err::NodePosition(k, p, v) => Err::NodePosition(k, str::from_utf8(p).unwrap(),
                                                            convert_vec(v)),
        }
    }

    fn convert_result<O,E>(res: IResult<&[u8],O,E>) -> IResult<&str,O,E> {
        match res {
            IResult::Done(i, o)    => IResult::Done(str::from_utf8(i).unwrap(), o),
            IResult::Error(e)      => IResult::Error(convert_err(e)),
            IResult::Incomplete(n) => IResult::Incomplete(n),
        }
    }

    macro_rules! assert_parse {
        ($res: expr, $expected: expr) => {
            match convert_result($res) {
                IResult::Done(i, actual) => assert_eq!((i,actual), ("", $expected)),
                IResult::Error(e)        => panic!(format!("{:?}", e)),
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
        assert_parse!(sp!(&b"/*before*/X /* between */\t\r\n /*asf*/ Y /*after*/"[..], pair!(char!('X'), char!('Y'))),
                      ('X', 'Y'));
    
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
        assert_parse!(enum_decl(b" enum { red(3), blue(5), white(7) } Color;"), color);
        let taste = TypeDecl {
            name: "Taste".to_string(),
            typ: TypeDeclType::Enum {
                elements: vec![("sweet".to_string(),  EnumValue::Literal(1)),
                               ("sour".to_string(),   EnumValue::Literal(2)),
                               ("bitter".to_string(), EnumValue::Literal(4))],
                max: Some(32000),
            },
        };
        assert_parse!(enum_decl(b"enum { sweet(1), sour(2), bitter(4), (32000) } Taste;"), taste);
        let reserved = TypeDecl {
            name: "Reserved".to_string(),
            typ: TypeDeclType::Enum {
                elements: vec![("foo".to_string(), EnumValue::Literal(1)),
                               ("reserved".to_string(), EnumValue::Range(Range { lower: 300, upper: 400 }))],
                max: Some(65535),
            },
        };
        assert_parse!(enum_decl(b"enum { foo(1), reserved(300..400), (65535) } Reserved;"), reserved);
    }

    #[test]
    fn check_struct_decl() {
        let v1 = TypeDecl {
            name: "V1".to_string(),
            typ:  TypeDeclType::Struct {
                fields: vec![
                    StructElement::Field(FieldDecl {
                        base: "uint16".to_string(),
                        name: "number".to_string(),
                        typ:  FieldType::ScalarType,
                    }),
                    StructElement::Field(FieldDecl {
                        base: "opaque".to_string(),
                        name: "string".to_string(),
                        typ:  FieldType::VariableVectorType(Range {lower: 0, upper: 10}),
                    })
                ],
            },
        };
        let v1_str = b"struct {
    uint16 number;
    opaque string<0..10>; /* variable length */
} V1;";
        assert_parse!(struct_decl(v1_str), v1);
        let v2 = TypeDecl {
            name: "V2".to_string(),
            typ:  TypeDeclType::Struct {
                fields: vec![
                    StructElement::Field(FieldDecl {
                        base: "uint32".to_string(),
                        name: "number".to_string(),
                        typ:  FieldType::ScalarType,
                    }),
                    StructElement::Field(FieldDecl {
                        base: "opaque".to_string(),
                        name: "string".to_string(),
                        typ:  FieldType::FixedVectorType(Constant::Literal(10)),
                    })
                ],
            },
        };
        let v2_str = b"struct {
    uint32 number;
    opaque string[10];     /* fixed length */
} V2;";
        assert_parse!(struct_decl(v2_str), v2);
        let variant_record = TypeDecl {
            name: "VariantRecord".to_string(),
            typ:  TypeDeclType::Struct {
                fields: vec![
                    StructElement::Field(FieldDecl {
                        base: "VariantTag".to_string(),
                        name: "type".to_string(),
                        typ:  FieldType::ScalarType,
                    }),
                    StructElement::Variant(VariantDecl {
                        selector: Name::Qualified("VariantRecord".to_string(), "type".to_string()),
                        cases:    vec![
                            ("apple".to_string(),  FieldDecl { base: "V1".to_string(), name: String::new(), typ: FieldType::ScalarType }),
                            ("orange".to_string(), FieldDecl { base: "V2".to_string(), name: String::new(), typ: FieldType::ScalarType })
                        ],
                    }),
                ],
            }
        };
        let vr_str = b"struct {
    VariantTag type;
    select (VariantRecord.type) {
        case apple:  V1;
        case orange: V2;
    };
} VariantRecord;";
        assert_parse!(struct_decl(vr_str), variant_record);
    }
}

// vim: tw=80:
