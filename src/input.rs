//! utilities and structs for scanning text files, translating them into symbols for the parser

use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::str::Chars;

struct Input {
    line_reader: io::Lines<io::BufReader<File>>,
    current_line: Option<Line>,
    line_num: u32,
}

#[self_referencing]
struct Line {
    string: String,
    #[borrows(string)]
    #[covariant]
    char_iterator: Chars<'this>,
    pos: u32,
}

impl Line {
    pub fn next(&mut self) -> Option<char> {
        self.with_mut(|fields| {
            *fields.pos = *fields.pos + 1;
            return fields.char_iterator.next();
        })
    }
}

impl Input {
    pub fn new<P: AsRef<Path>>(filename: P) -> io::Result<Self> {
        let file = File::open(filename)?;
        let line_reader = io::BufReader::new(file).lines();
        Ok(Self {
            line_reader,
            current_line: None,
            line_num: 0,
        })
    }

    pub fn next(&mut self) -> Option<char> {
        loop {
            if let Some(line) = &mut self.current_line {
                if let Some(character) = line.next() {
                    return Some(character);
                }
            }
            // if there is no line yet, or if it has been depleted, a new one needs to be read
            if let Some(line_result) = self.line_reader.next() {
                self.line_num += 1;
                let line = line_result.expect(&*format!("couldn't read line: {}", self.line_num));
                self.current_line = Some(LineBuilder {
                    string: line,
                    char_iterator_builder: |line: &String| line.chars(),
                    pos: 0,
                }.build());
            } else {
                // if no new line can be read then we've reached the end and return `None`
                return None;
            }
        }
    }
}