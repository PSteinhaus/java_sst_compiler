//! This module covers the basic need to read in text files character per character.
//! Sadly, this can be a bit of a pain in Rust...

use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::str::Chars;

pub type LNum = u32;
pub type CPos = u32;

/// A struct for simply reading in text files character per character.
pub struct Input {
    line_reader: io::Lines<io::BufReader<File>>,
    current_line: Option<Line>,
    line_num: LNum,
    /// This field is a buffer for the peeked next character of the stream.
    ///
    /// - If it's `None`, then the current character hasn't been peeked.
    /// - If it's `Some(Some(_))`, then the current character has been peeked and is valid
    /// - If it's `Some(None)`, then the current character has been peeked, but it's invalid, i.e. there is no next character (EOF)
    peeked_char: Option<Option<CharWithPos>>,
}

/// This struct holds the line, which is currently being read, as a String.
/// As it also holds an iterator to that String, it's a self referencing struct, which aren't directly
/// supported by Rust yet, so we make use of the [`ouroboros`](https://docs.rs/ouroboros/0.13.0/ouroboros/index.html) crate
/// to be able to create it safely without too much hassle anyway.
#[self_referencing]
struct Line {
    string: String,
    #[borrows(string)]
    #[covariant]
    char_iterator: Chars<'this>,
    pos: CPos,
}

impl Line {
    /// Returns the next character from the line, or `None` if the line has been read to completion.
    pub fn next(&mut self) -> Option<char> {
        // with_mut is a method created automatically by ouroboros to access all fields of this struct
        // sadly, using such methods is necessary as the macro transforms `Line` into a new struct, for
        // which it's no longer allowed to access the fields directly in the usual way
        self.with_mut(|fields| {
            *fields.pos += 1;
            fields.char_iterator.next()
        })
    }
    /// Returns the position of the last character read from this line.
    pub fn pos(&self) -> CPos {
        // borrow_pos is another method created by ouroboros (see `next`)
        *self.borrow_pos()
    }
}

/// This struct bundles a character with the number of the line where it has been read and the
/// position inside that line.
#[derive(Debug, Copy, Clone)]
pub struct CharWithPos {
    pub ch: char,
    pub pos: CPos,
    pub line: LNum,
}

impl Input {
    pub fn new<P: AsRef<Path>>(filepath: P) -> io::Result<Self> {
        let file = File::open(filepath)?;
        let line_reader = io::BufReader::new(file).lines();
        Ok(Self {
            line_reader,
            current_line: None,
            line_num: 0,
            peeked_char: None,
        })
    }

    /// Returns the next character of the file without advancing beyond it.
    pub fn peek(&mut self) -> Option<CharWithPos> {
        if self.peeked_char.is_none() {
            self.peeked_char = Some(self.next());
        }
        self.peeked_char.unwrap()
    }

    /// Simply reads in an returns the next character of the file, if one exists.
    ///
    /// If no more characters are to be read it returns `None`.
    pub fn next(&mut self) -> Option<CharWithPos> {
        // if there's already a char buffered from peeking it then return that first
        // and make sure the buffer is cleared
        if self.peeked_char.is_some() {
            let ch = std::mem::replace(&mut self.peeked_char, None);
            return ch.unwrap();
        }
        loop {
            let mut first_line = true;
            let mut line_end_pos = 0;
            if let Some(line) = &mut self.current_line {
                first_line = false;
                if let Some(character) = line.next() {
                    return Some(CharWithPos {
                        ch: character,
                        pos: line.pos(),
                        line: self.line_num,
                    });
                } else {
                    line_end_pos = line.pos();
                }
            }
            // if there is no line yet, or if it has been depleted, a new one needs to be read
            if let Some(line_result) = self.line_reader.next() {
                self.line_num += 1;
                let line = line_result.expect(&*format!("couldn't read line: {}", self.line_num));
                self.current_line = Some(
                    LineBuilder {
                        string: line,
                        char_iterator_builder: |line: &String| line.chars(),
                        pos: 0,
                    }
                    .build(),
                );
                if !first_line {
                    // if this is not the first line ever read, return a line break
                    return Some(CharWithPos {
                        ch: '\n',
                        pos: line_end_pos,
                        line: self.line_num - 1, // the line break was on the line before
                    });
                }
            } else {
                // if no new line can be read then we've reached the end and return `None`
                return None;
            }
        }
    }
}
