mod helper;
mod input;
mod parser;
mod scanner;

#[macro_use]
extern crate ouroboros;

pub type SSTint = i32;

use crate::input::Input;
use crate::parser::Parser;
use crate::scanner::Scanner;
use std::{env, path};

fn main() {
    let args: Vec<String> = env::args().skip(1).collect(); // skip the program name
    if args.is_empty() {
        // display help
        println!("Usage: java_sst_compiler [--scanner | -s] [--dot-rep | -d] source");
        return;
    }

    let mut show_dot = false;
    let mut show_scanner_tokens = false;
    let mut filepath = None;
    for arg in args {
        match arg {
            flag if flag.starts_with("--dot-rep") || flag.starts_with("-d") => {
                show_dot = true;
            }
            flag if flag.starts_with("--scanner") || flag.starts_with("-s") => {
                show_scanner_tokens = true;
            }
            path => {
                filepath = Some(path);
            }
        }
    }

    if filepath.is_none() {
        println!("Please enter the path to your source file");
        return;
    }
    let filepath = filepath.unwrap();

    if show_scanner_tokens {    // this is not exactly pretty, but the scanner is consumed, so this is the easiest way to do this
        let input = Input::new(path::PathBuf::from(&filepath)).expect(format!("file {} not found", &filepath).as_str());
        let mut scanner = Scanner::new(input);
        println!("scanner token stream:");
        println!();
        while let Some(sym) = scanner.read_token() {
            println!("{:?}", sym);
        }
        println!();
    }

    let input = Input::new(path::PathBuf::from(&filepath)).expect(format!("file {} not found", filepath).as_str());
    let scanner = Scanner::new(input);

    let parser = Parser::new(scanner);
    match parser.parse() {
        Ok((_sym_table, ast)) => {
            if show_dot {
                println!("dot representation of the abstract syntax tree:");
                println!();
                println!("{}", ast.dot_representation());
                println!();
            }
            let result = crate::parser::semantic::check(&ast);
            if let Err(e) = result {
                panic!("{}", e.to_string());
            }
            // generate the bytecode!
            crate::parser::bytecode::generate(&ast).expect("couldn't create the bytecode");
        }
        Err(e) => panic!("{}", e.to_string()),
    }
}
