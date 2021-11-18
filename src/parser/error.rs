use crate::input::{CPos, LNum};
use crate::parser::Symbol;
use crate::scanner::{TWithPos, Token};
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};

pub trait ParseError: Error {}

pub type ParseResult = Result<(), Box<dyn ParseError>>;

#[derive(Debug)]
pub struct SymbolError {
    symbol: Symbol,
    cause: Option<Box<dyn ParseError>>,
}

impl SymbolError {
    pub fn new(symbol: Symbol) -> Self {
        Self {
            symbol,
            cause: None,
        }
    }
    pub fn new_with_cause(symbol: Symbol, cause: Box<dyn ParseError>) -> Self {
        Self {
            symbol,
            cause: Some(cause),
        }
    }
}

impl Display for SymbolError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "ParseError {:?}", self)
    }
}

impl Error for SymbolError {}

impl ParseError for SymbolError {}

#[derive(Debug)]
pub struct UnexpectedEndOfTokens {
    line: LNum,
    pos: CPos,
}

impl UnexpectedEndOfTokens {
    pub fn new(line: LNum, pos: CPos) -> Self {
        Self { line, pos }
    }
}

impl Error for UnexpectedEndOfTokens {}
impl ParseError for UnexpectedEndOfTokens {}

impl Display for UnexpectedEndOfTokens {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "expected another token at line {}, position {}",
            self.line, self.pos
        )
    }
}

#[derive(Debug)]
pub struct WrongToken {
    token: TWithPos,
    expected_variants: Vec<Token>,
}

impl WrongToken {
    pub fn new(token: TWithPos, expected_variants: Vec<Token>) -> Self {
        Self {
            token,
            expected_variants,
        }
    }
}

impl Error for WrongToken {}
impl ParseError for WrongToken {}

impl Display for WrongToken {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "expected token variants {:?} at line {}, position {},\
            actually got: {:?}",
            self.expected_variants, self.token.line, self.token.pos, self.token.token
        )
    }
}

#[derive(Debug)]
pub struct SymbolsNotFound {
    expected_variants: Vec<Symbol>,
}

impl SymbolsNotFound {
    pub fn new(expected_variants: Vec<Symbol>) -> Self {
        Self { expected_variants }
    }
}

impl Error for SymbolsNotFound {}
impl ParseError for SymbolsNotFound {}

impl Display for SymbolsNotFound {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "couldn't find any of the expected symbol variants {:?}",
            self.expected_variants
        )
    }
}
