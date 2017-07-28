#[macro_use]
extern crate nom;

mod parse;

use std::{env, process};
use std::string::String;
use std::fs::File;
use std::io::{self, BufReader};
use std::io::prelude::*;
use std::error::Error;

//use parse::{TypeDecl, parse_types};
use parse::parse_types;


macro_rules! die {
    ($msg: expr) => {{
        eprintln!("{}", $msg);
        process::exit(1);
    }};
    ($msg: expr, $err: expr) => {{
        eprintln!("{}: {}", $msg, $err.description());
        process::exit(1);
    }};
}


fn extract_definitions(path: &str) -> io::Result<Vec<(usize, String)>> {
    let     file = File::open(path)?;
    let     reader = BufReader::new(file);
    let mut defns: Vec<(usize, String)> = Vec::new();
    let mut defn: Vec<String> = Vec::new();
    let mut def_start = 0;
    let mut in_def = false;

    for (line_num, line) in reader.lines().enumerate() {
        let line = line?;
        if in_def {
            if line.is_empty() || line.starts_with(" ") || line.starts_with("\t") {
                defn.push(line);
                continue;
            }
            // We're done with this definition block. Add it to the results.
            defns.push((def_start, defn.join("\n")));
            defn.clear();
            in_def = false;
        }
        // One could have ended and another begun.
        if !in_def && line.starts_with("%%% ") {
            in_def = true;
            def_start = line_num + 1;
        }
    }
    Ok(defns)
}

fn main() {
    if env::args().count() != 2 {
        die!(&format!("Usage: {} FILE", env::args().next().unwrap()));
    }
    let path = env::args().last().unwrap();
    let definitions = extract_definitions(&path)
        .unwrap_or_else(|err| die!(&path, err));


    for (line_num, text) in definitions {
        match parse_types(&text) {
            Err(err) => {
                println!("{}:{} Parser returned an error: {}", path, line_num, err);
            },
            Ok((types, rest)) => {
                if !types.is_empty() {
                    println!("From line {}, parsed:", line_num);
                    for typ in types.iter() {
                        //println!("{:#?}", typ);
                        println!("\t{}", typ.name);
                    }
                }
                if !rest.is_empty() {
                    println!("From line {}, failed to parse:\n{}",
                             line_num, rest);
                }
            }
        };
    }
}

// vim: tw=80:
