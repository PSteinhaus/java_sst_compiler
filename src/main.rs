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
use std::path;

fn main() {
    let input = Input::new(path::PathBuf::from("parsetest.txt")).unwrap();
    let scanner = Scanner::new(input);
    let parser = Parser::new(scanner);
    match parser.parse() {
        Ok((_sym_table, ast)) => {
            println!("{}", ast.dot_representation());
            let result = crate::parser::semantic::check(&ast);
            if let Err(e) = result {
                panic!("{}", e.to_string());
            }
        }
        Err(e) => panic!("{}", e.to_string()),
    }
    /*
    while let Some(sym) = scanner.read_token() {
        println!("{:?}", sym);
    }
    */
}
