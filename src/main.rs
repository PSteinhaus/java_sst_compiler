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
    let (_sym_table, ast) = parser.parse().unwrap();
    println!("{}", ast.dot_representation());
    /*
    while let Some(sym) = scanner.read_token() {
        println!("{:?}", sym);
    }
    */
}
