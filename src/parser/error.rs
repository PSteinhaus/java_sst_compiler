use crate::input::{CPos, LNum};
use crate::parser::Symbol;
use crate::scanner::{TWithPos, Token};
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use dyn_clone::{clone_trait_object, DynClone};

pub trait ParseError: Error + DynClone {}

clone_trait_object!(ParseError);    // creates a DynClone implementation that just creates a new dynamic object based on a clone of the specific ParseError object

pub type CheckResult = Result<(), Box<dyn ParseError>>;
pub type ParseResult = Result<(), Box<dyn ParseError>>;
/// contains the symbol enum that was actually parsed
pub type ParseMultiResult = Result<Symbol, Box<dyn ParseError>>;

#[derive(Debug, Clone)]
pub struct SymbolError {
    symbol: Symbol,
    cause: Option<Box<dyn ParseError>>,
}

impl SymbolError {
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

#[derive(Debug, Copy, Clone)]
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

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
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


#[derive(Debug, Clone)]
pub struct DoubleDeclaration {
    name: String,
}

impl DoubleDeclaration {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl Error for DoubleDeclaration {}
impl ParseError for DoubleDeclaration {}

impl Display for DoubleDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "double declaration of {:?}",
            self.name
        )
    }
}

#[derive(Debug, Clone)]
pub struct UndefinedSymbol {
    name: String,
}

impl UndefinedSymbol {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl Error for UndefinedSymbol {}
impl ParseError for UndefinedSymbol {}

impl Display for UndefinedSymbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} has not been defined yet",
            self.name
        )
    }
}