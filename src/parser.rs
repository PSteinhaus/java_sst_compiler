//! functionality for parsing symbols returned by the scanner
//!
//! this includes syntax-checking and the creation of the AST

mod error;
mod sym_table;

use crate::input::{CPos, LNum};
use crate::parser::error::*;
use crate::parser::sym_table::{Type, ResultType, SymEntry, SymTable, EntryType};
use crate::scanner;
use crate::scanner::Token::{
    Comma, CurlyClose, CurlyOpen, Divide, Else, Equals, EqualsEquals, Final, If, Int, Larger,
    LargerEqual, Minus, ParClose, ParOpen, Plus, Public, Return, Semicolon, Smaller, SmallerEqual,
    Times, Void, While,
};
use crate::scanner::{TWithPos, Token};
use std::cell::RefCell;
use std::collections::VecDeque;
use std::mem::discriminant as d;
use std::ops::Deref;
use std::rc::Rc;
use crate::parser::Symbol::TokenSym;

#[derive(Debug, Clone)]
pub enum Symbol {
    Class,
    Classbody,
    Declarations,
    FinalDeclaration, // added to make implementation easier
    NonFinalDeclaration, // added
    MethodDeclaration,
    MethodHead,
    MethodType,
    FormalParameters,
    FpSection,
    MethodBody,
    LocalDeclaration,
    StatementSequence,
    Statement,
    Type,
    Assignment,
    ProcedureCall,
    InternProcedureCall,
    IfStatement,
    WhileStatement,
    ReturnStatement,
    ActualParameters,
    Expression,
    SimpleExpression,
    Term,
    Factor,
    TokenSym(Token),
}

struct Queue<T: Clone> {
    queue: VecDeque<T>,
    /// the index pointing to the next item in the buffer
    pub next_index: usize,
}

impl<T: Clone> Queue<T> {
    pub fn new() -> Self {
        Self {
            queue: VecDeque::<T>::new(),
            next_index: 0,
        }
    }

    fn get_next(&self) -> Option<T> {
        self.queue.get(self.next_index).map(|t| (*t).clone())
    }

    pub fn peek<I: Iterator<Item = T>>(&mut self, iter: &mut I) -> Option<T> {
        // if you've already stored a peek (i.e. the item found at the next index) return it
        if let Some(item) = self.get_next() {
            return Some(item);
        }
        // if not then you have to read in a new one
        if let Some(new_item) = self.read(iter) {
            return Some(new_item);
        }
        // if no new item can be read return None
        None
    }

    pub fn next<I: Iterator<Item = T>>(&mut self, iter: &mut I) -> Option<T> {
        // return the next object (which is the same as the current peek)
        let item = self.peek(iter);
        //and advance the index
        self.next_index += 1;

        item
    }

    /// Advance the index pointing to the next item by 1, without reading in new items.
    pub fn advance(&mut self) {
        self.next_index += 1;
    }
    /*
        /// Decrement the index pointing to the next item by n.
        pub fn go_back(&mut self, n: usize) {
            assert!(n <= self.next_index);
            self.next_index -= n;
        }
    */
    /// Remove all items previous to the next item (if any) from the buffer.
    pub fn clear_previous(&mut self) {
        self.queue.drain(..self.next_index).for_each(drop);
        self.next_index = 0;
    }

    /// Read in new items from the iterator until you hold next_index+1 elements.
    ///
    /// Then return the item at next_index, if there is one.
    fn read<I: Iterator<Item = T>>(&mut self, iter: &mut I) -> Option<T> {
        //println!("index: {}", self.next_index);
        //println!("len before: {}", self.queue.len());
        while self.queue.len() <= self.next_index {
            if let Some(item) = iter.next() {
                self.queue.push_back(item);
            } else {
                return None;
            }
        }
        //println!("len after: {}", self.queue.len());
        self.get_next()
    }
}

pub struct Parser<I: Iterator<Item = TWithPos>> {
    t_iter: I,
    token_buffer: Queue<TWithPos>,
    line: LNum,
    pos: CPos,
    //ast: Node,
    sym_table: Rc<RefCell<SymTable>>,
    sym_table_current: Rc<RefCell<SymTable>>,
}

impl<I> Parser<I>
where
    I: Iterator<Item = TWithPos>,
{
    pub fn new(t_iter: I) -> Self {
        let head_table = Rc::new(RefCell::new(SymTable::new(None)));
        Self {
            t_iter,
            token_buffer: Queue::<TWithPos>::new(),
            line: 0,
            pos: 0,
            sym_table: head_table.clone(),
            sym_table_current: head_table,
        }
    }

    pub fn line(&self) -> LNum {
        self.line
    }

    pub fn pos(&self) -> CPos {
        self.pos
    }

    /// Consume the parser to parse the given Input.
    pub fn parse(mut self) -> ParseResult {
        // the starting symbol is "class"
        self.parse_symbol(Symbol::Class)
    }

    /// Try interpreting the token stream as the given symbol.
    ///
    /// Build an AST and a matching symbol table.
    pub fn parse_symbol(&mut self, symbol: Symbol) -> ParseResult {
        self.parse_symbol_ext(symbol, None)
    }

    /// Try interpreting the token stream as the given symbol.
    ///
    /// Build an AST and a matching symbol table.
    ///
    /// This variant also takes a Vec to collect added symbol table entry names (in case we have to remove them later).
    pub fn parse_symbol_ext(&mut self, symbol: Symbol, added_sym_names: Option<&mut Vec<String>>) -> ParseResult {
        use Symbol::*;
        let dummy_ident = scanner::Token::Ident("".to_string());
        let dummy_number = scanner::Token::Number(0);
        let mut new_sym_name_vec = Vec::new();  // doesn't actually allocate anything as long as it's not needed
        let added_sym_names = added_sym_names.unwrap_or(&mut new_sym_name_vec);
        let index_before = self.token_buffer.next_index;
        let current_sym_table_before = self.sym_table_current.clone();

        let mut try_parse = || -> ParseResult {
            match symbol.clone() {
                Class => {
                    self.try_symbol(TokenSym(scanner::Token::Class))?;
                    let class_name = self.parse_identifier()?;

                    let weak_enclose = Rc::downgrade(&self.sym_table_current);
                    let class_sym_table = Rc::new(RefCell::new(SymTable::new(Some(weak_enclose))));
                    let class_entry = SymEntry::new(class_name, EntryType::Class(class_sym_table.clone()));
                    self.add_sym_table_entry(class_entry, added_sym_names).expect("couldn't add class entry, probably due to duplicate class name (should never happen in JavaSST)");

                    // set the class sym table to be the current one, because we now dive into the class
                    self.sym_table_current = class_sym_table;
                    self.parse_symbol(Classbody)
                }
                Classbody => {
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    self.parse_symbol(Declarations)?;
                    self.try_symbol(TokenSym(CurlyClose))
                }
                Declarations => {
                    // start with the final declarations
                    while let Ok(()) = self.parse_symbol(FinalDeclaration) {}
                    // then get the non-final declarations
                    while let Ok(()) = self.parse_symbol(NonFinalDeclaration) {}
                    // then get the method declarations
                    while let Ok(()) = self.parse_symbol(MethodDeclaration) {}
                    Ok(())
                }
                FinalDeclaration => {
                    self.try_symbol(TokenSym(Final))?;
                    let p_type = self.parse_type()?;
                    let name = self.parse_identifier()?;
                    self.try_symbol(TokenSym(Equals))?;
                    self.parse_symbol(Expression)?;
                    self.try_symbol(TokenSym(Semicolon))?;

                    self.add_sym_table_entry(SymEntry::new(name, EntryType::Const(p_type)), added_sym_names)?;
                    Ok(())
                }
                NonFinalDeclaration => {
                    let p_type = self.parse_type()?;
                    let name = self.parse_identifier()?;
                    self.try_symbol(TokenSym(Semicolon))?;

                    self.add_sym_table_entry(SymEntry::new(name, EntryType::Var(p_type)), added_sym_names)?;
                    Ok(())
                }
                MethodDeclaration => {
                    let method_entry = self.parse_method_head()?;
                    let method_sym_table = method_entry.sym_table().unwrap().clone();
                    self.add_sym_table_entry(method_entry, added_sym_names)?;

                    // now we're diving into the method body so enter the method's sym table
                    self.sym_table_current = method_sym_table;
                    self.parse_symbol(MethodBody)
                }
                MethodHead => {
                    self.parse_method_head()?;
                    Ok(())
                }
                MethodType => {
                    self.parse_method_type()?;
                    Ok(())
                }
                FormalParameters => {
                    self.parse_formal_parameters()?;
                    Ok(())
                }
                FpSection => {
                    self.parse_fp_section()?;
                    Ok(())
                }
                MethodBody => {
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    // find all local declarations
                    while let Ok(()) = self.parse_symbol(LocalDeclaration) {}
                    // then the statement sequence
                    self.parse_symbol(StatementSequence)?;
                    self.try_symbol(TokenSym(CurlyClose))
                }
                LocalDeclaration => {
                    let d_type = self.parse_type()?;
                    let identifier = self.parse_identifier()?;
                    self.try_symbol(TokenSym(Semicolon))?;

                    let decl_entry = SymEntry::new(identifier, EntryType::Var(d_type));
                    self.add_sym_table_entry(decl_entry, added_sym_names)?;
                    Ok(())
                }
                StatementSequence => {
                    self.parse_symbol(Statement)?;
                    while let Ok(()) = self.parse_symbol(Statement) {}
                    Ok(())
                }
                Statement => {
                    self.parse_symbols(&[
                        Assignment,
                        ProcedureCall,
                        IfStatement,
                        WhileStatement,
                        ReturnStatement,
                    ])
                },
                Type => {
                    self.parse_type()?;
                    Ok(())
                },
                Assignment => {
                    let var_ident = self.parse_identifier()?;
                    self.try_symbol(TokenSym(Equals))?;
                    self.parse_symbol(Expression)?;
                    self.try_symbol(TokenSym(Semicolon))
                }
                ProcedureCall => {
                    self.parse_symbol(InternProcedureCall)?;
                    self.try_symbol(TokenSym(Semicolon))
                }
                InternProcedureCall => {
                    let procedure_name = self.parse_identifier()?;
                    self.parse_symbol(ActualParameters)
                }
                IfStatement => {
                    self.try_symbol(TokenSym(If))?;
                    self.try_symbol(TokenSym(ParOpen))?;
                    self.parse_symbol(Expression)?;
                    self.try_symbol(TokenSym(ParClose))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    // start a new block with it's own symbol table and add it as a new entry to the current sym table
                    let current_table = self.sym_table_current.clone();
                    let if_block_table = self.sym_table_current.borrow_mut().add_block(Rc::downgrade(&current_table))?;
                    // enter that table
                    self.sym_table_current = if_block_table;
                    // do things inside the block
                    self.parse_symbol(StatementSequence)?;
                    self.try_symbol(TokenSym(CurlyClose))?;
                    // leave the block
                    self.sym_table_current = current_table;
                    self.try_symbol(TokenSym(Else))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    // start a new block with it's own symbol table and add it as a new entry to the current sym table
                    let if_block_table = self.sym_table_current.borrow_mut().add_block(Rc::downgrade(&self.sym_table_current))?;
                    // enter that table
                    self.sym_table_current = if_block_table;
                    // do things inside the block
                    self.parse_symbol(StatementSequence)?;
                    self.try_symbol(TokenSym(CurlyClose))?;
                    // leaving the block is unnecessary as that happens at the end of parse_symbol anyway
                    Ok(())
                }
                WhileStatement => {
                    self.try_symbol(TokenSym(While))?;
                    self.try_symbol(TokenSym(ParOpen))?;
                    self.parse_symbol(Expression)?;
                    self.try_symbol(TokenSym(ParClose))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    // start a new block with it's own symbol table and add it as a new entry to the current sym table
                    let if_block_table = self.sym_table_current.borrow_mut().add_block(Rc::downgrade(&self.sym_table_current))?;
                    // enter that table
                    self.sym_table_current = if_block_table;
                    // do things inside the block
                    self.parse_symbol(StatementSequence)?;
                    self.try_symbol(TokenSym(CurlyClose))
                    // leaving the block is unnecessary as that happens at the end of parse_symbol anyway
                }
                ReturnStatement => {
                    self.try_symbol(TokenSym(Return))?;
                    if let Ok(()) = self.parse_symbol(SimpleExpression) {}
                    self.try_symbol(TokenSym(Semicolon))
                }
                ActualParameters => {
                    self.try_symbol(TokenSym(ParOpen))?;
                    if let Ok(()) = self.parse_symbol(Expression) {
                        // find all following expressions
                        while let Ok(()) = self.parse_sequence(&[TokenSym(Comma), Expression]) {}
                    }
                    self.try_symbol(TokenSym(ParClose))
                }
                Expression => {
                    self.parse_symbol(SimpleExpression)?;
                    if let Ok(()) = self.parse_symbols(&[
                        TokenSym(EqualsEquals),
                        TokenSym(Smaller),
                        TokenSym(SmallerEqual),
                        TokenSym(Larger),
                        TokenSym(LargerEqual),
                    ]) {
                        self.parse_symbol(SimpleExpression)?;
                    }
                    Ok(())
                }
                SimpleExpression => {
                    self.parse_symbol(Term)?;
                    while let Ok(()) = self.parse_symbols(&[TokenSym(Plus), TokenSym(Minus)]) {
                        self.parse_symbol(Term)?;
                    }
                    Ok(())
                }
                Term => {
                    self.parse_symbol(Factor)?;
                    while let Ok(()) = self.parse_symbols(&[TokenSym(Times), TokenSym(Divide)]) {
                        self.parse_symbol(Factor)?;
                    }
                    Ok(())
                }
                Factor => {
                    if let Err(_) = self.parse_symbols(&[
                        InternProcedureCall,
                        TokenSym(dummy_ident.clone()),
                        TokenSym(dummy_number.clone()),
                    ]) {
                        self.try_symbol(TokenSym(ParOpen))?;
                        self.parse_symbol(Expression)?;
                        return self.try_symbol(TokenSym(ParClose));
                    }
                    Ok(())
                }
                TokenSym(expected_token) => {
                    if let Ok(next_token) = self.next_token() {
                        if d(&next_token.token) == d(&expected_token) {
                            Ok(())
                        } else {
                            Err(Box::new(WrongToken::new(
                                next_token.clone(),
                                vec![expected_token],
                            )))
                        }
                    } else {
                        Err(self.end_of_token_error())
                    }
                }
            }
        };

        let p_res = try_parse();
        // set the symbol table that was current before parsing this symbol to be current again
        self.sym_table_current = current_sym_table_before;
        match p_res {
            Ok(()) => Ok(()),
            Err(e) => {
                //println!("Failed!");
                // reset the index so someone can try again with another symbol
                self.token_buffer.next_index = index_before;
                // remove all sym table entries added in the effort of parsing this symbol
                for name in added_sym_names {
                    self.sym_table_current.deref().borrow_mut().remove_entry(name.as_str());
                }

                Err(Box::new(SymbolError::new_with_cause(symbol, e)))
            }
        }
    }

    pub fn check_syntax(mut self) -> CheckResult {
        // the starting symbol is "class"
        self.try_symbol(Symbol::Class)
    }

    /// Try interpreting the token stream as one of the symbols. Try one after another.
    /// Stop as soon as you find the matching symbol.
    fn try_symbols(&mut self, expected_symbols: &[Symbol]) -> CheckResult {
        for sym in expected_symbols {
            if let Ok(()) = self.try_symbol((*sym).clone()) {
                return Ok(());
            }
        }
        Err(Box::new(SymbolsNotFound::new(
            expected_symbols.iter().map(|sym| (*sym).clone()).collect(),
        )))
    }

    /// Try interpreting the token stream as one of the symbols. Try one after another.
    /// Stop as soon as you find the matching symbol.
    fn parse_symbols(&mut self, expected_symbols: &[Symbol]) -> ParseResult {
        for sym in expected_symbols {
            if let Ok(()) = self.parse_symbol((*sym).clone()) {
                return Ok(());
            }
        }
        Err(Box::new(SymbolsNotFound::new(
            expected_symbols.iter().map(|sym| (*sym).clone()).collect(),
        )))
    }

    /// Try interpreting the token stream as the given sequence of symbols.
    /// Save the state of the buffer and restore it if you fail.
    fn try_sequence(&mut self, expected_sequence: &[Symbol]) -> CheckResult {
        let index_before = self.token_buffer.next_index;
        for sym in expected_sequence {
            if let Err(e) = self.try_symbol((*sym).clone()) {
                self.token_buffer.next_index = index_before;
                return Err(e);
            }
        }
        Ok(())
    }

    fn parse_sequence(&mut self, expected_sequence: &[Symbol]) -> ParseResult {
        let index_before = self.token_buffer.next_index;
        let mut added_sym_names = Vec::new();
        for sym in expected_sequence {
            if let Err(e) = self.parse_symbol_ext((*sym).clone(), Some(&mut added_sym_names)) {
                self.token_buffer.next_index = index_before;    // restart reading from the token buffer at the previous position
                return Err(e);
            }
        }
        Ok(())
    }

    /// Try interpreting the token stream as the given symbol.
    pub fn try_symbol(&mut self, symbol: Symbol) -> CheckResult {
        use Symbol::*;
        let dummy_ident = scanner::Token::Ident("".to_string());
        let dummy_number = scanner::Token::Number(0);
        let index_before = self.token_buffer.next_index;

        let mut try_check = || -> CheckResult {
            match symbol.clone() {
                Class => {
                    self.try_symbol(TokenSym(scanner::Token::Class))?;
                    self.try_symbol(TokenSym(dummy_ident.clone()))?;
                    self.try_symbol(Classbody)
                }
                Classbody => {
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    self.try_symbol(Declarations)?;
                    self.try_symbol(TokenSym(CurlyClose))
                }
                Declarations => {
                    // start with the final declarations
                    while let Ok(()) = self.try_symbol(FinalDeclaration) {}
                    // then get the non-final declarations
                    while let Ok(()) = self.try_symbol(NonFinalDeclaration) {}
                    // then get the method declarations
                    while let Ok(()) = self.try_symbol(MethodDeclaration) {}
                    Ok(())
                }
                FinalDeclaration => {
                    self.try_symbol(TokenSym(Final))?;
                    self.try_symbol(Type)?;
                    self.try_symbol(TokenSym(dummy_ident.clone()))?;
                    self.try_symbol(TokenSym(Equals))?;
                    self.try_symbol(Expression)?;
                    self.try_symbol(TokenSym(Semicolon))
                }
                NonFinalDeclaration => {
                    self.try_symbol(Type)?;
                    self.try_symbol(TokenSym(dummy_ident.clone()))?;
                    self.try_symbol(TokenSym(Semicolon))
                }
                MethodDeclaration => {
                    self.try_symbol(MethodHead)?;
                    self.try_symbol(MethodBody)
                }
                MethodHead => {
                    self.try_symbol(TokenSym(Public))?;
                    self.try_symbol(MethodType)?;
                    self.try_symbol(TokenSym(dummy_ident.clone()))?;
                    self.try_symbol(FormalParameters)
                }
                MethodType => {
                    if let Ok(()) = self.try_symbol(TokenSym(Void)) {
                        return Ok(());
                    } else {
                        self.try_symbol(Type)
                    }
                }
                FormalParameters => {
                    self.try_symbol(TokenSym(ParOpen))?;
                    // find all fp_sections
                    if let Ok(()) = self.try_symbol(FpSection) {
                        while let Ok(()) = self.try_sequence(&[TokenSym(Comma), FpSection]) {}
                    }
                    self.try_symbol(TokenSym(ParClose))?;
                    Ok(())
                }
                FpSection => {
                    self.try_symbol(Type)?;
                    self.try_symbol(TokenSym(dummy_ident.clone()))
                }
                MethodBody => {
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    // find all local declarations
                    while let Ok(()) = self.try_symbol(LocalDeclaration) {}
                    // then the statement sequence
                    self.try_symbol(StatementSequence)?;
                    self.try_symbol(TokenSym(CurlyClose))
                }
                LocalDeclaration => {
                    self.try_symbol(Type)?;
                    self.try_symbol(TokenSym(dummy_ident.clone()))?;
                    self.try_symbol(TokenSym(Semicolon))
                }
                StatementSequence => {
                    self.try_symbol(Statement)?;
                    while let Ok(()) = self.try_symbol(Statement) {}
                    Ok(())
                }
                Statement => self.try_symbols(&[
                    Assignment,
                    ProcedureCall,
                    IfStatement,
                    WhileStatement,
                    ReturnStatement,
                ]),
                Type => self.try_symbol(TokenSym(Int)),
                Assignment => {
                    self.try_symbol(TokenSym(dummy_ident.clone()))?;
                    self.try_symbol(TokenSym(Equals))?;
                    self.try_symbol(Expression)?;
                    self.try_symbol(TokenSym(Semicolon))
                }
                ProcedureCall => {
                    self.try_symbol(InternProcedureCall)?;
                    self.try_symbol(TokenSym(Semicolon))
                }
                InternProcedureCall => {
                    self.try_symbol(TokenSym(dummy_ident.clone()))?;
                    self.try_symbol(ActualParameters)
                }
                IfStatement => {
                    self.try_symbol(TokenSym(If))?;
                    self.try_symbol(TokenSym(ParOpen))?;
                    self.try_symbol(Expression)?;
                    self.try_symbol(TokenSym(ParClose))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    self.try_symbol(StatementSequence)?;
                    self.try_symbol(TokenSym(CurlyClose))?;
                    self.try_symbol(TokenSym(Else))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    self.try_symbol(StatementSequence)?;
                    self.try_symbol(TokenSym(CurlyClose))
                }
                WhileStatement => {
                    self.try_symbol(TokenSym(While))?;
                    self.try_symbol(TokenSym(ParOpen))?;
                    self.try_symbol(Expression)?;
                    self.try_symbol(TokenSym(ParClose))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    self.try_symbol(StatementSequence)?;
                    self.try_symbol(TokenSym(CurlyClose))
                }
                ReturnStatement => {
                    self.try_symbol(TokenSym(Return))?;
                    if let Ok(()) = self.try_symbol(SimpleExpression) {}
                    self.try_symbol(TokenSym(Semicolon))
                }
                ActualParameters => {
                    self.try_symbol(TokenSym(ParOpen))?;
                    if let Ok(()) = self.try_symbol(Expression) {
                        // find all following expressions
                        while let Ok(()) = self.try_sequence(&[TokenSym(Comma), Expression]) {}
                    }
                    self.try_symbol(TokenSym(ParClose))
                }
                Expression => {
                    self.try_symbol(SimpleExpression)?;
                    if let Ok(()) = self.try_symbols(&[
                        TokenSym(EqualsEquals),
                        TokenSym(Smaller),
                        TokenSym(SmallerEqual),
                        TokenSym(Larger),
                        TokenSym(LargerEqual),
                    ]) {
                        self.try_symbol(SimpleExpression)?;
                    }
                    Ok(())
                }
                SimpleExpression => {
                    self.try_symbol(Term)?;
                    while let Ok(()) = self.try_symbols(&[TokenSym(Plus), TokenSym(Minus)]) {
                        self.try_symbol(Term)?;
                    }
                    Ok(())
                }
                Term => {
                    self.try_symbol(Factor)?;
                    while let Ok(()) = self.try_symbols(&[TokenSym(Times), TokenSym(Divide)]) {
                        self.try_symbol(Factor)?;
                    }
                    Ok(())
                }
                Factor => {
                    if let Ok(()) = self.try_symbol(TokenSym(ParOpen)) {
                        self.try_symbol(Expression)?;
                        self.try_symbol(TokenSym(ParClose))
                    } else {
                        self.try_symbols(&[
                            InternProcedureCall,
                            TokenSym(dummy_ident.clone()),
                            TokenSym(dummy_number.clone()),
                        ])
                    }
                }
                TokenSym(expected_token) => {
                    if let Ok(next_token) = self.next_token() {
                        if d(&next_token.token) == d(&expected_token) {
                            Ok(())
                        } else {
                            Err(Box::new(WrongToken::new(
                                next_token.clone(),
                                vec![expected_token],
                            )))
                        }
                    } else {
                        Err(self.end_of_token_error())
                    }
                }
            }
        };

        match try_check() {
            Ok(()) => Ok(()),
            Err(e) => {
                // reset the index so someone can try again with another symbol
                //println!("Failed!");
                self.token_buffer.next_index = index_before;
                Err(Box::new(SymbolError::new_with_cause(symbol, e)))
            }
        }
    }

    fn next_token(&mut self) -> Result<TWithPos, Box<dyn ParseError>> {
        let next = self.peek_next_token()?;
        self.line = next.line;
        self.pos = next.pos;
        // advance the index
        self.token_buffer.advance();
        Ok(next)
    }

    fn peek_next_token(&mut self) -> Result<TWithPos, Box<dyn ParseError>> {
        if let Some(token) = self.token_buffer.peek(&mut self.t_iter) {
            return Ok(token);
        }
        // no more tokens available
        Err(self.end_of_token_error())
    }

    fn parse_method_head(&mut self) -> Result<SymEntry, Box<dyn ParseError>> {
        self.try_symbol(TokenSym(Public))?;
        let m_type = self.parse_method_type()?;
        let name = self.parse_identifier()?;
        let params = self.parse_formal_parameters()?;

        let weak_enclose = Rc::downgrade(&self.sym_table_current);
        let method_sym_table = Rc::new(RefCell::new(SymTable::new(Some(weak_enclose))));

        let method_sym_entry = SymEntry::new(name, EntryType::Proc(method_sym_table, params, m_type));

        Ok(method_sym_entry)
    }

    fn parse_formal_parameters(&mut self) -> Result<Vec<(Type, String)>, Box<dyn ParseError>> {
        // start the parameter list with the first param
        let mut p_list = vec![self.parse_fp_section()?];

        while let Ok(()) = self.try_symbol(TokenSym(Comma)) {
            // an additional parameter has been found; add it
            p_list.push(self.parse_fp_section()?);
        }

        Ok(p_list)
    }

    fn parse_fp_section(&mut self) -> Result<(Type, String), Box<dyn ParseError>> {
        let t = self.parse_type()?;
        let name = self.parse_identifier()?;
        Ok((t, name))
    }

    fn parse_method_type(&mut self) -> Result<ResultType, Box<dyn ParseError>> {
        let t_w_pos = self.next_token()?;
        match t_w_pos.token {
            Token::Void => {
                return Ok(ResultType::Void);
            }
            Token::Int => {
                return Ok(ResultType::Int);
            }
            _ => {
                Err(Box::new(WrongToken::new(
                    t_w_pos,
                    vec![Token::Int],
                )))
            }
        }
    }

    fn parse_identifier(&mut self) -> Result<String, Box<dyn ParseError>> {
        let t_w_pos = self.next_token()?;
        return if let Token::Ident(s) = t_w_pos.token {
            Ok(s)
        } else {
            Err(Box::new(WrongToken::new(
                t_w_pos,
                vec![Token::Ident("identifierName".to_string())],
            )))
        };
    }

    fn parse_type(&mut self) -> Result<Type, Box<dyn ParseError>> {
        let t_w_pos = self.next_token()?;
        match t_w_pos.token {
            Token::Int => {
                return Ok(Type::Int);
            }
            _ => {
                Err(Box::new(WrongToken::new(
                    t_w_pos,
                    vec![Token::Int],
                )))
            }
        }
    }

    /// This function creates a weak reference counted pointer to the current symbol table and uses
    /// it to create a new symbol table, which is enclosed by the current one.
    ///
    /// It then _enters_ that table by making it current.
    fn enter_new_table(&mut self) {
        let weak_enclose = Rc::downgrade(&self.sym_table_current);
        self.sym_table_current = Rc::new(RefCell::new(SymTable::new(Some(weak_enclose))));
    }

    fn add_sym_table_entry(&mut self, entry: SymEntry, added_sym_names: &mut Vec<String>) -> Result<(), Box<dyn ParseError>> {
        added_sym_names.push(entry.name().to_string());
        self.sym_table_current.borrow_mut().add_entry(entry)
    }

    fn end_of_token_error(&self) -> Box<UnexpectedEndOfTokens> {
        Box::new(UnexpectedEndOfTokens::new(self.line(), self.pos()))
    }
}