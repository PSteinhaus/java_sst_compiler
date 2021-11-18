mod input;
mod parser;
mod scanner;

#[macro_use]
extern crate ouroboros;

pub type SSTint = i32;

use crate::input::Input;
use crate::scanner::Scanner;
use std::path;
use crate::parser::Parser;

fn main() {
    let input = Input::new(path::PathBuf::from("scantest.txt")).unwrap();
    let scanner = Scanner::new(input);
    let mut parser = Parser::new(scanner);
    parser.check_syntax().unwrap();
    /*
    while let Some(sym) = scanner.read_token() {
        println!("{:?}", sym);
    }
    */
}
