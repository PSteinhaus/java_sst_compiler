//! functionality for parsing symbols returned by the scanner
//!
//! this includes syntax-checking and the creation of the AST

mod error;

use std::collections::VecDeque;
use crate::input::{CPos, LNum};
use crate::parser::error::*;
use crate::scanner;
use crate::scanner::{TWithPos, Token};
use std::mem::discriminant as d;
use crate::scanner::Token::{Comma, CurlyClose, CurlyOpen, Divide, Else, Equals, EqualsEquals, Final, If, Int, Larger, LargerEqual, Minus, ParClose, ParOpen, Plus, Public, Return, Semicolon, Smaller, SmallerEqual, Times, Void, While};

#[derive(Debug, Clone)]
pub enum Symbol {
    Class,
    Classbody,
    Declarations,
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
    Token(Token),
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

    fn get_next(&self) -> Option<T> { self.queue.get(self.next_index).map(|t| (*t).clone()) }

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
    pub fn advance(&mut self) { self.next_index += 1; }
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
}

impl<I> Parser<I>
where
    I: Iterator<Item = TWithPos>,
{
    pub fn new(t_iter: I) -> Self {
        Self {
            t_iter,
            token_buffer: Queue::<TWithPos>::new(),
            line: 0,
            pos: 0,
        }
    }

    pub fn line(&self) -> LNum {
        self.line
    }

    pub fn pos(&self) -> CPos {
        self.pos
    }

    pub fn check_syntax(&mut self) -> ParseResult {
        // the starting symbol is "class"
        self.try_symbol(Symbol::Class)
    }

    /// Try interpreting the token stream as one of the symbols. Try one after another.
    /// Stop as soon as you find the matching symbol.
    fn try_symbols(&mut self, expected_symbols: &[Symbol]) -> ParseResult {
        for sym in expected_symbols {
            if let Ok(()) = self.try_symbol((*sym).clone()) {
                return Ok(());
            }
        }
        Err(Box::new(SymbolsNotFound::new(expected_symbols.iter().map(|sym| (*sym).clone()).collect())))
    }

    /// Try interpreting the token stream as the given symbol.
    pub fn try_symbol(&mut self, symbol: Symbol) -> ParseResult {
        use Symbol::*;
        let dummy_ident = scanner::Token::Ident("".to_string());
        let dummy_number = scanner::Token::Number(0);
        let index_before = self.token_buffer.next_index;
        let mut try_check = || -> ParseResult {
            match symbol.clone() {
                Class => {
                    self.try_symbol(Token(scanner::Token::Class))?;
                    self.try_symbol(Token(dummy_ident.clone()))?;
                    self.try_symbol(Classbody)
                }
                Classbody => {
                    self.try_symbol(Token(CurlyOpen))?;
                    self.try_symbol(Declarations)?;
                    self.try_symbol(Token(CurlyClose))
                }
                Declarations => {
                    // start with the final declarations
                    loop {
                        let i_before = self.token_buffer.next_index;
                        let mut ok = true;
                        match self.try_symbol(Token(Final)) {
                            Ok(()) => {
                                if let Err(_) = self.try_symbol(Type) {ok = false;}
                                if let Err(_) = self.try_symbol(Token(dummy_ident.clone())) {ok = false;}
                                if let Err(_) = self.try_symbol(Token(Equals)) {ok = false;}
                                if let Err(_) = self.try_symbol(Expression) {ok = false;}
                                if let Err(_) = self.try_symbol(Token(Semicolon)) {ok = false;}
                            }
                            Err(_) => { ok = false; }
                        }
                        if !ok {
                            // error: this actually wasn't a final declaration
                            // return the buffer back to the state before trying to parse the token stream as one
                            self.token_buffer.next_index = i_before;
                            break;
                        }
                    }
                    // then get the non-final declarations
                    loop {
                        let i_before = self.token_buffer.next_index;
                        match self.try_symbol(Type) {
                            Ok(()) => {
                                self.try_symbol(Token(dummy_ident.clone()))?;
                                self.try_symbol(Token(Semicolon))?;
                            }
                            Err(_) => {
                                // error: this actually wasn't a non-final declaration
                                // return the buffer back to the state before trying to parse the token stream as one
                                self.token_buffer.next_index = i_before;
                                break;
                            }
                        }
                    }
                    // then get the method declarations
                    while let Ok(()) = self.try_symbol(MethodDeclaration) {}
                    Ok(())
                }
                MethodDeclaration => {
                    self.try_symbol(MethodHead)?;
                    self.try_symbol(MethodBody)
                }
                MethodHead => {
                    self.try_symbol(Token(Public))?;
                    self.try_symbol(MethodType)?;
                    self.try_symbol(Token(dummy_ident.clone()))?;
                    self.try_symbol(FormalParameters)
                }
                MethodType => {
                    if let Ok(()) = self.try_symbol(Token(Void)) { return Ok(()) }
                    else { self.try_symbol(Type) }
                }
                FormalParameters => {
                    self.try_symbol(Token(ParOpen))?;
                    // find all fp_sections
                    if let Ok(()) = self.try_symbol(FpSection) {
                        loop {
                            let i_before = self.token_buffer.next_index;
                            match self.try_symbol(Token(Comma)) {
                                Ok(()) => {
                                    self.try_symbol(FpSection)?;
                                }
                                Err(_) => {
                                    // error: this actually wasn't another fp_section
                                    // return the buffer back to the state before trying to parse the token stream as one
                                    self.token_buffer.next_index = i_before;
                                    break;
                                }
                            }
                        }
                    }
                    self.try_symbol(Token(ParClose))?;
                    Ok(())
                }
                FpSection => {
                    self.try_symbol(Type)?;
                    self.try_symbol(Token(dummy_ident.clone()))
                }
                MethodBody => {
                    self.try_symbol(Token(CurlyOpen))?;
                    // find all local declarations
                    while let Ok(()) = self.try_symbol(LocalDeclaration) {}
                    // then the statement sequence
                    self.try_symbol(StatementSequence)?;
                    self.try_symbol(Token(CurlyClose))
                }
                LocalDeclaration => {
                    self.try_symbol(Type)?;
                    self.try_symbol(Token(dummy_ident.clone()))?;
                    self.try_symbol(Token(Semicolon))
                }
                StatementSequence => {
                    self.try_symbol(Statement)?;
                    while let Ok(()) = self.try_symbol(Statement) {}
                    Ok(())
                }
                Statement => {
                    self.try_symbols(&[Assignment, ProcedureCall, IfStatement, WhileStatement, ReturnStatement])
                }
                Type => {
                    self.try_symbol(Token(Int))
                }
                Assignment => {
                    self.try_symbol(Token(dummy_ident.clone()))?;
                    self.try_symbol(Token(Equals))?;
                    self.try_symbol(Expression)?;
                    self.try_symbol(Token(Semicolon))
                }
                ProcedureCall => {
                    self.try_symbol(InternProcedureCall)?;
                    self.try_symbol(Token(Semicolon))
                }
                InternProcedureCall => {
                    self.try_symbol(Token(dummy_ident.clone()))?;
                    self.try_symbol(ActualParameters)
                }
                IfStatement => {
                    self.try_symbol(Token(If))?;
                    self.try_symbol(Token(ParOpen))?;
                    self.try_symbol(Expression)?;
                    self.try_symbol(Token(ParClose))?;
                    self.try_symbol(Token(CurlyOpen))?;
                    self.try_symbol(StatementSequence)?;
                    self.try_symbol(Token(CurlyClose))?;
                    self.try_symbol(Token(Else))?;
                    self.try_symbol(Token(CurlyOpen))?;
                    self.try_symbol(StatementSequence)?;
                    self.try_symbol(Token(CurlyClose))
                }
                WhileStatement => {
                    self.try_symbol(Token(While))?;
                    self.try_symbol(Token(ParOpen))?;
                    self.try_symbol(Expression)?;
                    self.try_symbol(Token(ParClose))?;
                    self.try_symbol(Token(CurlyOpen))?;
                    self.try_symbol(StatementSequence)?;
                    self.try_symbol(Token(CurlyClose))
                }
                ReturnStatement => {
                    self.try_symbol(Token(Return))?;
                    if let Ok(()) = self.try_symbol(SimpleExpression) {}
                    self.try_symbol(Token(Semicolon))
                }
                ActualParameters => {
                    self.try_symbol(Token(ParOpen))?;
                    if let Ok(()) = self.try_symbol(Expression) {
                        // find all following expressions
                        loop {
                            let i_before = self.token_buffer.next_index;
                            match self.try_symbol(Token(Comma)) {
                                Ok(()) => {
                                    self.try_symbol(Expression)?;
                                }
                                Err(_) => {
                                    // error: this actually wasn't another expression
                                    // return the buffer back to the state before trying to parse the token stream as one
                                    self.token_buffer.next_index = i_before;
                                    break;
                                }
                            }
                        }
                    }
                    self.try_symbol(Token(ParClose))
                }
                Expression => {
                    self.try_symbol(SimpleExpression)?;
                    if let Ok(()) = self.try_symbols(&[Token(EqualsEquals), Token(Smaller), Token(SmallerEqual), Token(Larger), Token(LargerEqual)]) {
                        self.try_symbol(SimpleExpression)?;
                    }
                    Ok(())
                }
                SimpleExpression => {
                    self.try_symbol(Term)?;
                    while let Ok(()) = self.try_symbols(&[Token(Plus), Token(Minus)]) {
                        self.try_symbol(Term)?;
                    }
                    Ok(())
                }
                Term => {
                    self.try_symbol(Factor)?;
                    while let Ok(()) = self.try_symbols(&[Token(Times), Token(Divide)]) {
                        self.try_symbol(Factor)?;
                    }
                    Ok(())
                }
                Factor => {
                    if let Ok(()) = self.try_symbol(Token(ParOpen)) {
                        self.try_symbol(Expression)?;
                        self.try_symbol(Token(ParClose))
                    } else {
                        self.try_symbols(&[InternProcedureCall, Token(dummy_ident.clone()), Token(dummy_number.clone())])
                    }
                }
                Token(expected_token) => {
                    if let Ok(next_token) = self.next_token() {
                        if d(&next_token.token) == d(&expected_token) {
                            Ok(())
                        } else {
                            Err(Box::new(WrongToken::new(next_token.clone(), vec![expected_token])))
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
            },
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

    fn end_of_token_error(&self) -> Box<UnexpectedEndOfTokens> {
        Box::new(UnexpectedEndOfTokens::new(
            self.line(),
            self.pos()
        ))
    }
}
