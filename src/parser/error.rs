use crate::input::{CPos, LNum};
use crate::parser::ast::SyntaxElement;
use crate::parser::sym_table::{EntryType, Type};
use crate::parser::Symbol;
use crate::scanner::{TWithPos, Token};
use dyn_clone::{clone_trait_object, DynClone};
use std::error::Error;
use std::fmt::{Debug, Display, Formatter};
use std::mem::Discriminant;

pub trait ParseError: Error + DynClone {}

clone_trait_object!(ParseError); // creates a DynClone implementation that just creates a new dynamic object based on a clone of the specific ParseError object

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
        write!(f, "double declaration of {:?}", self.name)
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
        write!(f, "{:?} has not been defined yet", self.name)
    }
}

#[derive(Debug, Clone)]
pub struct TypeMismatch {
    symbol_name: String,
    expected: String,
    found: Discriminant<EntryType>,
}

impl TypeMismatch {
    pub fn new(symbol_name: String, expected: String, found: Discriminant<EntryType>) -> Self {
        Self {
            symbol_name,
            expected,
            found,
        }
    }
}

impl Error for TypeMismatch {}
impl ParseError for TypeMismatch {}

impl Display for TypeMismatch {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} has type: {:?}\nexpected: {}",
            self.symbol_name, self.found, self.expected
        )
    }
}

#[derive(Debug, Clone)]
pub struct IncompatibleTypes {
    left_type: Type,
    right_type: Type,
    line: LNum,
    pos: CPos,
}

impl IncompatibleTypes {
    pub fn new(left_type: Type, right_type: Type, line: LNum, pos: CPos) -> Self {
        Self {
            left_type,
            right_type,
            line,
            pos,
        }
    }
}

impl Error for IncompatibleTypes {}
impl ParseError for IncompatibleTypes {}

impl Display for IncompatibleTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "left operand has type: {:?}, right operand has type: {:?} on line {}, pos {}",
            self.left_type, self.right_type, self.line, self.pos,
        )
    }
}

#[derive(Debug, Clone)]
pub struct VoidOperand {
    line: LNum,
    pos: CPos,
}

impl VoidOperand {
    pub fn new(line: LNum, pos: CPos) -> Self {
        Self { line, pos }
    }
}

impl Error for VoidOperand {}
impl ParseError for VoidOperand {}

impl Display for VoidOperand {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "tried to use void as an operand on line {}, pos {}",
            self.line, self.pos
        )
    }
}

#[derive(Debug, Clone)]
pub struct ArgumentMismatch {
    line: LNum,
    pos: CPos,
}

impl ArgumentMismatch {
    pub fn new(line: LNum, pos: CPos) -> Self {
        Self { line, pos }
    }
}

impl Error for ArgumentMismatch {}
impl ParseError for ArgumentMismatch {}

impl Display for ArgumentMismatch {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "arguments don't match parameters on line {}, pos {}",
            self.line, self.pos
        )
    }
}

#[derive(Debug, Clone)]
pub struct WrongOperandType {
    line: LNum,
    pos: CPos,
    wrong_type: Type,
    operator_type: SyntaxElement,
}

impl WrongOperandType {
    pub fn new(line: LNum, pos: CPos, wrong_type: Type, operator_type: SyntaxElement) -> Self {
        Self {
            line,
            pos,
            wrong_type,
            operator_type,
        }
    }
}

impl Error for WrongOperandType {}
impl ParseError for WrongOperandType {}

impl Display for WrongOperandType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "tried to use {:?} as an operand type for {:?} on line {}, pos {}",
            self.wrong_type, self.operator_type, self.line, self.pos
        )
    }
}

#[derive(Debug, Clone)]
pub struct WrongReturnType {
    line: LNum,
    pos: CPos,
    desired_type: Type,
}

impl WrongReturnType {
    pub fn new(line: LNum, pos: CPos, desired_type: Type) -> Self {
        Self {
            line,
            pos,
            desired_type,
        }
    }
}

impl Error for WrongReturnType {}
impl ParseError for WrongReturnType {}

impl Display for WrongReturnType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "function declared on line {}, pos {} doesn't always return the specified type of {:?}",
            self.line, self.pos, self.desired_type
        )
    }
}

#[derive(Debug, Clone)]
pub struct UninitializedVar {
    line: LNum,
    pos: CPos,
    name: String,
}

impl UninitializedVar {
    pub fn new(line: LNum, pos: CPos, name: String) -> Self {
        Self { line, pos, name }
    }
}

impl Error for UninitializedVar {}
impl ParseError for UninitializedVar {}

impl Display for UninitializedVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "variable {} on line {}, pos {} might not be initialized!",
            self.name, self.line, self.pos
        )
    }
}
