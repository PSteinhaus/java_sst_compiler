//! utilities and structs for scanning texts, translating them into symbols for the parser

use crate::input::{CPos, Input, LNum};
use crate::SSTint;

#[derive(Debug)]
pub enum Token {
    Class,
    Public,
    Void,
    If,
    Else,
    Int,
    While,
    Final,
    Return,

    Equals,
    EqualsEquals,
    Smaller,
    SmallerEqual,
    Larger,
    LargerEqual,

    CurlyOpen,
    CurlyClose,
    ParOpen,
    ParClose,
    Semicolon,
    Comma,
    Plus,
    Minus,
    Times,
    Divide,

    Ident(String),
    Number(SSTint),

    Other,
}

pub struct Scanner {
    input: Input,
}

use crate::scanner::Token::*;

impl Scanner {
    pub fn new(input: Input) -> Self {
        Self { input }
    }

    /// Returns the next symbol, if there is one, or `None`, if there isn't.
    pub fn read_sym(&mut self) -> Option<(Token, LNum, CPos)> {
        while let Some(next_char) = self.input.next() {
            // check if you hit whitespace and if true just continue with the next character
            if next_char.ch.is_whitespace() {
                continue;
            }
            let token = match next_char.ch {
                '{' => CurlyOpen,
                '}' => CurlyClose,
                '(' => ParOpen,
                ')' => ParClose,
                ';' => Semicolon,
                ',' => Comma,
                '+' => Plus,
                '-' => Minus,
                '*' => Times,
                '/' => {
                    if let Some(ch_w_p) = self.input.peek() {
                        if ch_w_p.ch == '*' {
                            self.input.next(); // read and throw away the '*'
                                               // this is the start of a comment
                                               // read characters until you come across another '*'
                            while let Some(comment_ch) = self.input.next() {
                                if comment_ch.ch == '*' {
                                    // peek the next symbol and if it's '/' read it and end the comment
                                    if let Some(following_ch) = self.input.peek() {
                                        if following_ch.ch == '/' {
                                            self.input.next();
                                            // call read_sym recursively to get the next symbol
                                            // (as this was just a comment)
                                            return self.read_sym();
                                        } else {
                                            continue;
                                        }
                                    }
                                    // end of input reached
                                    break;
                                }
                            }
                            // there's no more input, but the comment hasn't been closed yet...
                            // PANIC!
                            panic!(
                                "comment started on line {} hasn't been closed!",
                                ch_w_p.line
                            );
                        }
                    }
                    Divide
                }
                '=' => {
                    let mut t = Equals;
                    if let Some(ch_w_p) = self.input.peek() {
                        if ch_w_p.ch == '=' {
                            self.input.next(); // advance the stream without reading, as we know the char already
                            t = EqualsEquals;
                        }
                    }
                    t
                }
                '<' => {
                    let mut t = Smaller;
                    if let Some(ch_w_p) = self.input.peek() {
                        if ch_w_p.ch == '=' {
                            self.input.next();
                            t = SmallerEqual
                        }
                    }
                    t
                }
                '>' => {
                    let mut t = Larger;
                    if let Some(ch_w_p) = self.input.peek() {
                        if ch_w_p.ch == '=' {
                            self.input.next();
                            t = LargerEqual
                        }
                    }
                    t
                }
                letter if letter.is_ascii_alphabetic() => {
                    // read all following alphanumeric characters and create a string from them
                    let mut s = letter.to_string();
                    while let Some(ch_w_pos) = self.input.peek() {
                        if ch_w_pos.ch.is_ascii_alphanumeric() {
                            s += ch_w_pos.ch.to_string().as_str();
                            self.input.next();
                        } else {
                            break;
                        }
                    }
                    // check whether the produced string is a keyword
                    match s.as_str() {
                        "class" => Class,
                        "public" => Public,
                        "void" => Void,
                        "if" => If,
                        "else" => Else,
                        "int" => Int,
                        "while" => While,
                        "final" => Final,
                        "return" => Return,
                        name => Ident(name.to_string()),
                    }
                }
                number if number.is_ascii_digit() => {
                    // read all following numeric characters and create a string from them
                    let mut n = number.to_string();
                    while let Some(ch_w_pos) = self.input.peek() {
                        if ch_w_pos.ch.is_ascii_digit() {
                            n += ch_w_pos.ch.to_string().as_str();
                            self.input.next();
                        } else {
                            break;
                        }
                    }
                    Number(n.parse::<SSTint>().unwrap())
                }
                _ => Other,
            };
            return Some((token, next_char.line, next_char.pos));
        }
        None
    }
}
