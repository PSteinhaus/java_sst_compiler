//! functionality for parsing symbols returned by the scanner
//!
//! this includes syntax-checking and the creation of the AST

mod error;
mod sym_table;
mod ast;

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
use std::cell::{RefCell};
use std::collections::VecDeque;
use std::fmt::Debug;
use std::mem::discriminant as d;
use std::ops::Deref;
use std::rc::Rc;
use crate::parser::ast::{Binop, Node, SyntaxElement};
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
    ast: Node,
    sym_table: Rc<RefCell<SymTable>>,
    sym_table_current: Rc<RefCell<SymTable>>,
    best_line: LNum,
    best_pos: CPos,
    best_error: Option<Box<dyn ParseError>>,
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
            ast: Node::new(SyntaxElement::Class, None, None),   // just a placeholder
            sym_table: head_table.clone(),
            sym_table_current: head_table,
            best_line: 0,
            best_pos: 0,
            best_error: None,
        }
    }

    pub fn line(&self) -> LNum {
        self.line
    }

    pub fn pos(&self) -> CPos {
        self.pos
    }

    /// Consume the parser to parse the given Input.
    pub fn parse(mut self) -> Result<(Rc<RefCell<SymTable>>, Node), Box<dyn ParseError>> {
        // the starting symbol is "class"
        // create a dummy node to put into parse_symbol
        let mut dummy = Node::new(SyntaxElement::Init, None, None);
        let res = self.parse_symbol(Symbol::Class, &mut dummy);
        if let Err(e) = res {
            // print the error that stopped the parser from progressing beyond the furthest it has ever read
            // (which is hopefully the error that actually caused the final failure)
            eprintln!("Parsing failed, probable source at line {}, pos {}, {}", self.best_line, self.best_pos, self.best_error.unwrap().deref().to_string());
            return Err(e);
        } else {
            // try to find all missing symbol table links in the ast
            self.ast.resolve_table_links()?;
            Ok((self.sym_table, self.ast))
        }
    }

    /// Try interpreting the token stream as the given symbol.
    ///
    /// Build an AST and a matching symbol table.
    pub fn parse_symbol(&mut self, symbol: Symbol, current_node: &mut Node) -> ParseResult {
        self.parse_symbol_ext(symbol, current_node, None, None)
    }

    /// Try interpreting the token stream as the given symbol.
    ///
    /// Build an AST and a matching symbol table.
    ///
    /// This variant also takes a Vec to collect added symbol table entry names (in case we have to remove them later)
    /// and possibly a hint as to where the next node should be added.
    fn parse_symbol_ext(&mut self, symbol: Symbol, current_node: &mut Node, added_sym_names: Option<&mut Vec<String>>, node_hint: Option<NodeHint>) -> ParseResult {
        use Symbol::*;
        let dummy_ident = scanner::Token::Ident("".to_string());
        let dummy_number = scanner::Token::Number(0);

        let mut new_sym_name_vec = Vec::new();  // doesn't actually allocate anything as long as it's not needed
        let added_sym_names = added_sym_names.unwrap_or(&mut new_sym_name_vec);
        let mut new_node_additions = NodeAdditions::new();
        let node_additions = &mut new_node_additions;
        let index_before = self.token_buffer.next_index;
        let current_sym_table_before = self.sym_table_current.clone();

        let mut try_parse = || -> ParseResult {
            match symbol.clone() {
                Class => {
                    self.try_symbol(TokenSym(scanner::Token::Class))?;
                    let class_name = self.parse_identifier()?;

                    let weak_enclose = Rc::downgrade(&self.sym_table_current);
                    let class_sym_table = Rc::new(RefCell::new(SymTable::new(Some(weak_enclose))));
                    let class_entry = Rc::new(RefCell::new(SymEntry::new(class_name, EntryType::Class(class_sym_table.clone()))));
                    self.add_sym_table_entry(class_entry.clone(), added_sym_names).expect("couldn't add class entry, probably due to duplicate class name (should never happen in JavaSST)");

                    // start the ast
                    let mut first_node = Node::new(SyntaxElement::Class, None, Some(class_entry));

                    // set the class sym table to be the current one, because we now dive into the class
                    self.sym_table_current = class_sym_table;
                    let res = self.parse_symbol(Classbody, &mut first_node);
                    self.ast = first_node;
                    res
                }
                Classbody => {
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    self.parse_symbol(Declarations, current_node)?;
                    self.try_symbol(TokenSym(CurlyClose))
                }
                Declarations => {
                    // start with the final declarations
                    let mut init_node = Node::new(SyntaxElement::Init, None, None);
                    if let Ok(()) = self.parse_symbol(FinalDeclaration, &mut init_node) {
                        let mut assign_node = init_node.borrow_left_mut().unwrap();
                        while let Ok(()) = self.parse_symbol(FinalDeclaration, assign_node) {
                            assign_node = assign_node.borrow_link_mut().unwrap();
                        }
                    }
                    // then get the non-final declarations
                    while let Ok(()) = self.parse_symbol(NonFinalDeclaration, &mut init_node) {}    // non-final declarations shouldn't need to touch the node
                    add_node_left(current_node, init_node, node_additions);
                    // then get the method declarations
                    if let Ok(()) = self.parse_symbol(MethodDeclaration, current_node) {
                        let mut enter_node = current_node.borrow_right_mut().unwrap();
                        while let Ok(()) = self.parse_symbol(MethodDeclaration, enter_node) {
                            enter_node = enter_node.borrow_link_mut().unwrap();
                        }
                    }
                    Ok(())
                }
                FinalDeclaration => {
                    let mut assign_node = Node::new(SyntaxElement::Assign, None, None);

                    self.try_symbol(TokenSym(Final))?;
                    let p_type = self.parse_type()?;
                    let name = self.parse_identifier()?;
                    let entry = Rc::new(RefCell::new(SymEntry::new(name, EntryType::Const(p_type))));
                    let const_node = Node::new(SyntaxElement::Var, None, Some(entry.clone()));
                    assign_node.set_left(Some(const_node));
                    self.try_symbol(TokenSym(Equals))?;

                    self.parse_symbol_ext(Expression, &mut assign_node, None, Some(NodeHint::Right))?;
                    self.try_symbol(TokenSym(Semicolon))?;

                    self.add_sym_table_entry(entry.clone(), added_sym_names)?;

                    // now we need some context to know where we to add the assignment to
                    match current_node.node_type() {
                        SyntaxElement::Init => {
                            add_node_left(current_node, assign_node, node_additions);
                        },
                        SyntaxElement::Assign => {
                            add_node_link(current_node, assign_node, node_additions);
                        }
                        _ => panic!("final declaration found while neither in init node, nor in assign node")
                    }

                    Ok(())
                }
                NonFinalDeclaration => {
                    let p_type = self.parse_type()?;
                    let name = self.parse_identifier()?;
                    self.try_symbol(TokenSym(Semicolon))?;

                    let entry = Rc::new(RefCell::new(SymEntry::new(name, EntryType::Var(p_type))));
                    self.add_sym_table_entry(entry, added_sym_names)?;
                    Ok(())
                }
                MethodDeclaration => {
                    let method_entry = self.parse_method_head()?;
                    let method_sym_table = method_entry.deref().borrow().sym_table().unwrap().clone();
                    self.add_sym_table_entry(method_entry.clone(), added_sym_names)?;

                    let mut enter_node = Node::new(SyntaxElement::Enter, None, Some(method_entry));

                    // now we're diving into the method body so enter the method's sym table
                    self.sym_table_current = method_sym_table;
                    self.parse_symbol(MethodBody, &mut enter_node)?;

                    // now we need some context to know where to add the assignment to
                    match current_node.node_type() {
                        SyntaxElement::Class => {
                            add_node_right(current_node, enter_node, node_additions);
                        },
                        SyntaxElement::Enter => {
                            add_node_link(current_node, enter_node, node_additions);
                        }
                        _ => panic!("method declaration found while neither in class node, nor in enter node")
                    }
                    Ok(())
                }
                MethodHead => {
                    panic!("case should never be reached, all is handled in MethodDeclaration");
                    //self.parse_method_head()?;
                    //Ok(())
                }
                MethodType => {
                    panic!("case should never be reached, all is handled in parse_method_head");
                    //self.parse_method_type()?;
                    //Ok(())
                }
                FormalParameters => {
                    panic!("case should never be reached, all is handled in parse_method_head");
                    //self.parse_formal_parameters()?;
                    //Ok(())
                }
                FpSection => {
                    panic!("case should never be reached, all is handled in parse_method_head");
                    //self.parse_fp_section()?;
                    //Ok(())
                }
                MethodBody => {
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    // find all local declarations
                    while let Ok(()) = self.parse_symbol(LocalDeclaration, current_node) {}
                    // then the statement sequence
                    self.parse_symbol_ext(StatementSequence, current_node, None, Some(NodeHint::Right))?;
                    self.try_symbol(TokenSym(CurlyClose))
                }
                LocalDeclaration => {
                    let d_type = self.parse_type()?;
                    let identifier = self.parse_identifier()?;
                    self.try_symbol(TokenSym(Semicolon))?;

                    let decl_entry = Rc::new(RefCell::new(SymEntry::new(identifier, EntryType::Var(d_type))));
                    self.add_sym_table_entry(decl_entry, added_sym_names)?;
                    Ok(())
                }
                StatementSequence => {
                    self.parse_symbol_ext(Statement, current_node, None, node_hint)?;
                    let stat_node = match node_hint.expect("stat sequences need node hints") {
                        NodeHint::Left => current_node.borrow_left_mut().unwrap(),
                        NodeHint::Right => current_node.borrow_right_mut().unwrap(),
                        NodeHint::Link => current_node.borrow_link_mut().unwrap(),
                    };
                    while let Ok(()) = self.parse_symbol_ext(Statement, stat_node, None, Some(NodeHint::Link)) {}
                    Ok(())
                }
                Statement => {
                    match self.parse_symbols_ext(&[
                        Assignment,
                        ProcedureCall,
                        IfStatement,
                        WhileStatement,
                        ReturnStatement,
                    ], current_node, node_hint) {
                        Ok(_) => Ok(()),
                        Err(e) => Err(e)
                    }
                },
                Type => {
                    self.parse_type()?;
                    Ok(())
                },
                Assignment => {
                    let var_ident = self.parse_identifier()?;
                    let en = self.sym_table_current.deref().borrow().get_entry(var_ident.as_str());
                    if let Some(entry) = en {
                        let var_node = Node::new(SyntaxElement::Var, None, Some(entry));
                        let mut assign_node = Node::new(SyntaxElement::Assign, None, None);
                        assign_node.set_left(Some(var_node));

                        self.try_symbol(TokenSym(Equals))?;
                        self.parse_symbol_ext(Expression, &mut assign_node, None, Some(NodeHint::Right))?;
                        self.try_symbol(TokenSym(Semicolon))?;

                        add_node_with_hint(current_node, assign_node, node_additions, node_hint.expect("assignments need node hints"));
                    } else {
                        return Err(Box::new(UndefinedSymbol::new(var_ident)));
                    }
                    Ok(())
                }
                ProcedureCall => {
                    self.parse_symbol_ext(InternProcedureCall, current_node, None, node_hint)?;
                    self.try_symbol(TokenSym(Semicolon))
                }
                InternProcedureCall => {
                    let procedure_name = self.parse_identifier()?;
                    let en = self.sym_table_current.deref().borrow().get_entry(procedure_name.as_str());
                    let ast_entry = if let Some(entry) = en {
                        entry
                    } else {
                        // don't throw an error when a procedure isn't defined (yet) because it might get defined later...
                        // instead add a placeholder allowing to try and resolve the missing link later
                        let placeholder = EntryType::Unresolved(Rc::downgrade(&self.sym_table_current));
                        Rc::new(RefCell::new(SymEntry::new(procedure_name, placeholder)))
                        //return Err(Box::new(UndefinedSymbol::new(procedure_name)));
                    };
                    let mut call_node = Node::new(SyntaxElement::Call, None, Some(ast_entry));
                    // set the actual parameters as the left child of the call node
                    self.parse_symbol_ext(ActualParameters, &mut call_node, None, Some(NodeHint::Left))?;

                    add_node_with_hint(current_node, call_node, node_additions, node_hint.expect("proc calls need a hint"));

                    Ok(())
                }
                IfStatement => {
                    self.try_symbol(TokenSym(If))?;
                    self.try_symbol(TokenSym(ParOpen))?;

                    let mut if_else_node = Node::new(SyntaxElement::IfElse, None, None);
                    let mut if_node = Node::new(SyntaxElement::If, None, None);

                    self.parse_symbol_ext(Expression, &mut if_node, None, Some(NodeHint::Left))?;

                    self.try_symbol(TokenSym(ParClose))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;

                    // start a new block with it's own symbol table and add it as a new entry to the current sym table
                    let current_table = self.sym_table_current.clone();
                    let (if_block_table, block_name) = self.sym_table_current.deref().borrow_mut().add_block(Rc::downgrade(&current_table))?;
                    added_sym_names.push(block_name);
                    // enter that table
                    self.sym_table_current = if_block_table;
                    // do things inside the block
                    self.parse_symbol_ext(StatementSequence, &mut if_node, None, Some(NodeHint::Right))?;
                    self.try_symbol(TokenSym(CurlyClose))?;
                    // leave the block
                    self.sym_table_current = current_table;
                    if_else_node.set_left(Some(if_node));

                    self.try_symbol(TokenSym(Else))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    // start a new block with it's own symbol table and add it as a new entry to the current sym table
                    let (if_block_table, block_name) = self.sym_table_current.deref().borrow_mut().add_block(Rc::downgrade(&self.sym_table_current))?;
                    added_sym_names.push(block_name);
                    // enter that table
                    self.sym_table_current = if_block_table;
                    // do things inside the block
                    self.parse_symbol_ext(StatementSequence, &mut if_else_node, None, Some(NodeHint::Right))?;
                    self.try_symbol(TokenSym(CurlyClose))?;

                    add_node_with_hint(current_node, if_else_node, node_additions, node_hint.expect("if needs node hints"));
                    // leaving the block is unnecessary as that happens at the end of parse_symbol anyway
                    Ok(())
                }
                WhileStatement => {
                    self.try_symbol(TokenSym(While))?;
                    self.try_symbol(TokenSym(ParOpen))?;

                    let mut while_node = Node::new(SyntaxElement::While, None, None);
                    self.parse_symbol_ext(Expression, &mut while_node, None, Some(NodeHint::Left))?;

                    self.try_symbol(TokenSym(ParClose))?;
                    self.try_symbol(TokenSym(CurlyOpen))?;
                    // start a new block with it's own symbol table and add it as a new entry to the current sym table
                    let (while_block_table, block_name) = self.sym_table_current.deref().borrow_mut().add_block(Rc::downgrade(&self.sym_table_current))?;
                    added_sym_names.push(block_name);

                    // enter that table
                    self.sym_table_current = while_block_table;
                    // do things inside the block
                    self.parse_symbol_ext(StatementSequence, &mut while_node, None, Some(NodeHint::Right))?;
                    self.try_symbol(TokenSym(CurlyClose))?;

                    add_node_with_hint(current_node, while_node, node_additions, node_hint.expect("while needs a node hint"));
                    // leaving the block is unnecessary as that happens at the end of parse_symbol anyway
                    Ok(())
                }
                ReturnStatement => {
                    self.try_symbol(TokenSym(Return))?;
                    let mut return_node = Node::new(SyntaxElement::Return, None, None);
                    if let Ok(()) = self.parse_symbol_ext(SimpleExpression, &mut return_node, None, Some(NodeHint::Right)) {}
                    self.try_symbol(TokenSym(Semicolon))?;

                    add_node_with_hint(current_node, return_node, node_additions, node_hint.expect("return needs a node hint"));
                    Ok(())
                }
                ActualParameters => {
                    self.try_symbol(TokenSym(ParOpen))?;
                    if let Ok(()) = self.parse_symbol_ext(Expression, current_node, None, node_hint) {
                        // borrow the added expression node from the current node in order to be able to pass it on and add links to the following expressions
                        let first_expr_node = borrow_node_with_hint(current_node, node_hint.expect("params need a hint")).unwrap();
                        // find all following expressions
                        while let Ok(()) = self.parse_sequence(&[TokenSym(Comma), Expression], first_expr_node, Some(NodeHint::Link)) {}
                        node_additions.mark_with_hint(node_hint.unwrap());
                    }
                    self.try_symbol(TokenSym(ParClose))
                }
                Expression => {
                    // first go with the assumption that this expression is no binary operation
                    self.parse_symbol_ext(SimpleExpression, current_node, None, node_hint.clone())?;
                    let hint = node_hint.expect("expressions always need a hint where to add their nodes");
                    if let Ok(symbol_found) = self.parse_symbols(&[
                        TokenSym(EqualsEquals),
                        TokenSym(Smaller),
                        TokenSym(SmallerEqual),
                        TokenSym(Larger),
                        TokenSym(LargerEqual),
                    ], current_node) {
                        // now we know that it IS a binop, so we need to instead create a binop node and add the previous simple expression as its left child
                        let mut binop_node = Node::new(SyntaxElement::Binop(match symbol_found {
                            TokenSym(EqualsEquals) => { Binop::Equals },
                            TokenSym(Smaller) => { Binop::Smaller },
                            TokenSym(SmallerEqual) => { Binop::SmallerEqual },
                            TokenSym(Larger) => { Binop::Larger },
                            TokenSym(LargerEqual) => { Binop::LargerEqual },
                            _ => panic!("parsed something different than a comparator for some reason")
                        }), None, None);
                        let s_expr_node = take_node_with_hint(current_node, hint);
                        binop_node.set_left_boxed(s_expr_node.unwrap()); // s_expr_node should exist as the first assumption should have lead to it being added
                        self.parse_symbol_ext(SimpleExpression, &mut binop_node, None, Some(NodeHint::Right))?;
                        add_node_with_hint(current_node, binop_node, node_additions, hint);
                    }
                    Ok(())
                }
                SimpleExpression => unsafe {
                    // first go with the assumption that this simple expression is no binary operation
                    self.parse_symbol_ext(Term, current_node, None, node_hint.clone())?;
                    let hint = node_hint.expect("simple expressions always need a hint where to add their nodes");
                    let mut binop_opt: Option<*mut Node> = None;
                    while let Ok(symbol_found) = self.parse_symbols(&[TokenSym(Plus), TokenSym(Minus)], current_node) {
                        // now we know that it IS a binop, so we need to instead create a binop node and add the previous term as its left child
                        let binop_node = Node::new(SyntaxElement::Binop(match symbol_found {
                            TokenSym(Plus) => { Binop::Add },
                            TokenSym(Minus) => { Binop::Sub },
                            _ => panic!("parsed something different than a plus or minus for some reason")
                        }), None, None);
                        // the previous term might currently be stored in the current node, or in the previous binop_node, depending on whether there was one
                        let (term_node, binop_ptr) = if let Some(previous_binop_ptr) = binop_opt {
                            let previous_binop = previous_binop_ptr.as_mut().unwrap();
                            let t_node = take_node_with_hint(previous_binop, NodeHint::Right);
                            previous_binop.set_right(Some(binop_node));
                            (t_node, previous_binop.borrow_right_mut().unwrap() as *mut Node)
                        } else {
                            let t_node = take_node_with_hint(current_node, hint);
                            add_node_with_hint(current_node, binop_node, node_additions, hint);
                            (t_node, current_node.borrow_right_mut().unwrap() as *mut Node)
                        };
                        (*binop_ptr).set_left_boxed(term_node.unwrap()); // term_node should exist as the first assumption should have lead to it being added
                        // now assume that the following term is indeed the last one of this simple expression and therefore add it as the right child of the binop
                        self.parse_symbol_ext(Term, &mut (*binop_ptr), None, Some(NodeHint::Right))?;
                        // but in case there is more, store the binop_node so that we might be able to take that right node away from it and make it the left node of the next binop
                        binop_opt = Some(binop_ptr);
                    }
                    Ok(())
                }
                Term => unsafe {
                    // first go with the assumption that this term is no binary operation
                    self.parse_symbol_ext(Factor, current_node, None, node_hint.clone())?;
                    let hint = node_hint.expect("terms always need a hint where to add their nodes");
                    let mut binop_opt: Option<*mut Node> = None;
                    while let Ok(symbol_found) = self.parse_symbols(&[TokenSym(Times), TokenSym(Divide)], current_node) {
                        // now we know that it IS a binop, so we need to instead create a binop node and add the previous factor as its left child
                        let binop_node = Node::new(SyntaxElement::Binop(match symbol_found {
                            TokenSym(Times) => { Binop::Mul },
                            TokenSym(Divide) => { Binop::Div },
                            _ => panic!("parsed something different than a times or divide for some reason")
                        }), None, None);
                        // the previous term might currently be stored in the current node, or in the previous binop_node, depending on whether there was one
                        let (factor_node, binop_ptr) = if let Some(previous_binop_ptr) = binop_opt {
                            let previous_binop = previous_binop_ptr.as_mut().unwrap();
                            let f_node = take_node_with_hint(previous_binop, NodeHint::Right);
                            previous_binop.set_right(Some(binop_node));
                            (f_node, previous_binop.borrow_right_mut().unwrap() as *mut Node)
                        } else {
                            let f_node = take_node_with_hint(current_node, hint);
                            add_node_with_hint(current_node, binop_node, node_additions, hint);
                            (f_node, current_node.borrow_right_mut().unwrap() as *mut Node)
                        };
                        (*binop_ptr).set_left_boxed(factor_node.unwrap()); // factor_node should exist as the first assumption should have lead to it being added
                        // now assume that the following factor is indeed the last one of this term and therefore add it as the right child of the binop
                        self.parse_symbol_ext(Factor, &mut (*binop_ptr), None, Some(NodeHint::Right))?;
                        // but in case there is more, store the binop_node so that we might be able to take that right node away from it and make it the left node of the next binop
                        binop_opt = Some(binop_ptr);
                    }
                    Ok(())
                }
                Factor => {
                    let mut call_node = Node::new(SyntaxElement::Call, None, None);
                    if let Ok(()) = self.parse_symbol_ext(InternProcedureCall, &mut call_node, None, node_hint) {
                        add_node_with_hint(current_node, call_node, node_additions, node_hint.expect("factors always need node hints"));
                    } else {
                        drop(call_node);
                        let mut var_node = Node::new(SyntaxElement::Var, None, None);
                        if let Ok(()) = self.parse_symbol(TokenSym(dummy_ident.clone()), &mut var_node) {
                            add_node_with_hint(current_node, var_node, node_additions, node_hint.expect("factors always need node hints"));
                        } else {
                            drop(var_node);
                            let mut const_node = Node::new(SyntaxElement::Const, None, None);
                            if let Ok(()) = self.parse_symbol(TokenSym(dummy_number.clone()), &mut const_node) {
                                add_node_with_hint(current_node, const_node, node_additions, node_hint.expect("factors always need node hints"));
                            } else {
                                drop(const_node);
                                self.try_symbol(TokenSym(ParOpen))?;
                                self.parse_symbol_ext(Expression, current_node, None, node_hint)?;
                                return self.try_symbol(TokenSym(ParClose));
                            }
                        }
                    }
                    Ok(())
                }
                TokenSym(expected_token) => {
                    if let Ok(next_token) = self.next_token() {
                        if d(&next_token.token) == d(&expected_token) {
                            match current_node.node_type() {
                                SyntaxElement::Call => {
                                    if let TWithPos { token: Token::Ident(s), .. } = next_token { // should always be true, due to the previous discriminant test
                                        // find the matching call symbol in the symbol table
                                        //println!("searching for entry {}", s.as_str());
                                        //println!("symbol table {:?}", self.sym_table_current.deref());
                                        let call_entry = self.sym_table_current.deref().borrow().get_entry(s.as_str());
                                        if let Some(entry) = call_entry {
                                            let sym_entry = entry.deref().borrow();
                                            let entry_type = sym_entry.entry_type();
                                            if let EntryType::Proc(..) = entry_type {  // check if the entry is actually a procedure
                                                drop(sym_entry);
                                                current_node.set_obj(Some(entry));
                                            } else {
                                                return Err(Box::new(TypeMismatch::new(s, "EntryType::Proc".to_string() ,d(entry_type))));
                                            };
                                        } else {
                                            // don't throw an error and instead just assume that the method will get defined later
                                            let unresolved_entry = EntryType::Unresolved(Rc::downgrade(&self.sym_table_current));
                                            current_node.set_obj(Some(Rc::new(RefCell::new(SymEntry::new(s, unresolved_entry)))))
                                            //return Err(Box::new(UndefinedSymbol::new(s)));    // old behavior: throw an error
                                        }
                                    }
                                }
                                SyntaxElement::Var => {
                                    if let TWithPos { token: Token::Ident(s), .. } = next_token {
                                        // find the matching var symbol in the symbol table
                                        //println!("searching for entry {}", s.as_str());
                                        //println!("symbol table {:?}", self.sym_table_current.deref());
                                        let var_entry = self.sym_table_current.deref().borrow().get_entry(s.as_str());
                                        if let Some(entry) = var_entry {
                                            // check if it's a constant
                                            {
                                                let sym_entry = entry.deref().borrow();
                                                let entry_type = sym_entry.entry_type();
                                                match entry_type {
                                                    EntryType::Const(value) => {
                                                        current_node.set_return_val(Some(*value));  // and set the return value to the const value if true
                                                    },
                                                    EntryType::Var(_) => {},
                                                    other_type => {
                                                        return Err(Box::new(TypeMismatch::new(s, "EntryType::Val or EntryType::Const".to_string(), d(other_type))));
                                                    }
                                                }
                                            }
                                            current_node.set_obj(Some(entry));
                                        } else {
                                            return Err(Box::new(UndefinedSymbol::new(s)));
                                        }
                                    }
                                }
                                SyntaxElement::Const => {
                                    if let TWithPos { token: Token::Number(i), .. } = next_token {
                                        current_node.set_return_val(Some(sym_table::Type::Int(i)));
                                    } else { panic!("token has wrong type for const") } // should never happen, but I keep it here in case more types get added
                                }
                                _ => {}
                            }
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
            Ok(()) => {
                // check if you now were able to parse more of the text successfully than up until now
                if self.line > self.best_line || (self.line == self.best_line && self.pos > self.best_pos) {
                    // yes, ok then make that the new best
                    self.best_line = self.line;
                    self.best_pos = self.pos;
                }
                Ok(())
            },
            Err(e) => {
                // reset the index so we can try again with another symbol
                self.token_buffer.next_index = index_before;
                // remove all sym table entries added in the effort of parsing this symbol
                for name in added_sym_names {
                    self.sym_table_current.deref().borrow_mut().remove_entry(name.as_str());
                }
                // remove all new nodes that were added to the current node
                if node_additions.left  { current_node.set_left(None); }
                if node_additions.right { current_node.set_right(None); }
                if node_additions.link  { current_node.set_link(None); }

                // check if you read further than ever before before encountering this error
                // if you did than this error is the new "best error"
                if self.line > self.best_line || (self.line == self.best_line && self.pos > self.best_pos) {
                    self.best_error = Some(Box::new(SymbolError::new_with_cause(symbol.clone(), e.clone())));
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
    fn parse_symbols_ext(&mut self, expected_symbols: &[Symbol], current_node: &mut Node, node_hint: Option<NodeHint>) -> ParseMultiResult {
        for sym in expected_symbols {
            if let Ok(()) = self.parse_symbol_ext((*sym).clone(), current_node, None, node_hint) {
                return Ok((*sym).clone());
            }
        }
        Err(Box::new(SymbolsNotFound::new(
            expected_symbols.iter().map(|sym| (*sym).clone()).collect(),
        )))
    }

    /// Try interpreting the token stream as one of the symbols. Try one after another.
    /// Stop as soon as you find the matching symbol.
    fn parse_symbols(&mut self, expected_symbols: &[Symbol], current_node: &mut Node) -> ParseMultiResult {
        self.parse_symbols_ext(expected_symbols, current_node, None)
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

    fn parse_sequence(&mut self, expected_sequence: &[Symbol], current_node: &mut Node, node_hint: Option<NodeHint>) -> ParseResult {
        let index_before = self.token_buffer.next_index;
        let mut added_sym_names = Vec::new();
        for sym in expected_sequence {
            if let Err(e) = self.parse_symbol_ext((*sym).clone(), current_node, Some(&mut added_sym_names), node_hint) {
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

    fn parse_method_head(&mut self) -> Result<Rc<RefCell<SymEntry>>, Box<dyn ParseError>> {
        self.try_symbol(TokenSym(Public))?;
        let m_type = self.parse_method_type()?;
        let name = self.parse_identifier()?;

        let weak_enclose = Rc::downgrade(&self.sym_table_current);
        let method_sym_table = Rc::new(RefCell::new(SymTable::new(Some(weak_enclose))));

        let params = self.parse_formal_parameters()?;
        // add the params to the method sym table
        for (t, name) in params.iter() {
            method_sym_table.deref().borrow_mut().add_entry(Rc::new(RefCell::new(SymEntry::new(name.clone(), EntryType::Var(*t)))))?;
        }

        let method_sym_entry = Rc::new(RefCell::new(SymEntry::new(name, EntryType::Proc(method_sym_table, params, m_type))));

        Ok(method_sym_entry)
    }

    fn parse_formal_parameters(&mut self) -> Result<Vec<(Type, String)>, Box<dyn ParseError>> {
        self.try_symbol(TokenSym(ParOpen))?;
        // start the parameter list with the first param
        let mut p_list = vec![];
        if let Ok(first_fp) = self.parse_fp_section() {
            p_list.push(first_fp);
            while let Ok(()) = self.try_symbol(TokenSym(Comma)) {
                // an additional parameter has been found; add it
                p_list.push(self.parse_fp_section()?);
            }
        }
        self.try_symbol(TokenSym(ParClose))?;

        Ok(p_list)
    }

    fn parse_fp_section(&mut self) -> Result<(Type, String), Box<dyn ParseError>> {
        let t = self.parse_type()?;
        let name = self.parse_identifier()?;
        Ok((t, name))
    }

    fn parse_method_type(&mut self) -> Result<ResultType, Box<dyn ParseError>> {
        let i_before = self.token_buffer.next_index;
        let t_w_pos = self.next_token()?;
        match t_w_pos.token {
            Token::Void => {
                return Ok(ResultType::Void);
            }
            Token::Int => {
                return Ok(ResultType::Int);
            }
            _ => {
                self.token_buffer.next_index = i_before;
                Err(Box::new(WrongToken::new(
                    t_w_pos,
                    vec![Token::Int],
                )))
            }
        }
    }

    fn parse_identifier(&mut self) -> Result<String, Box<dyn ParseError>> {
        let i_before = self.token_buffer.next_index;
        let t_w_pos = self.next_token()?;
        return if let Token::Ident(s) = t_w_pos.token {
            Ok(s)
        } else {
            self.token_buffer.next_index = i_before;
            Err(Box::new(WrongToken::new(
                t_w_pos,
                vec![Token::Ident("identifierName".to_string())],
            )))
        };
    }

    fn parse_type(&mut self) -> Result<Type, Box<dyn ParseError>> {
        let i_before = self.token_buffer.next_index;
        let t_w_pos = self.next_token()?;
        match t_w_pos.token {
            Token::Int => {
                return Ok(Type::Int(0));    // 0 is just a placeholder
            }
            _ => {
                self.token_buffer.next_index = i_before;
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

    fn add_sym_table_entry(&mut self, entry: Rc<RefCell<SymEntry>>, added_sym_names: &mut Vec<String>) -> Result<(), Box<dyn ParseError>> {
        added_sym_names.push(entry.deref().borrow().name().to_string());
        self.sym_table_current.deref().borrow_mut().add_entry(entry)
    }

    fn end_of_token_error(&self) -> Box<UnexpectedEndOfTokens> {
        Box::new(UnexpectedEndOfTokens::new(self.line(), self.pos()))
    }
}

fn add_node_left(current_node: &mut Node, child: Node, node_additions: &mut NodeAdditions) {
    current_node.set_left(Some(child));
    node_additions.left = true;
}

fn add_node_right(current_node: &mut Node, child: Node, node_additions: &mut NodeAdditions) {
    current_node.set_right(Some(child));
    node_additions.right = true;
}

fn add_node_link(current_node: &mut Node, link: Node, node_additions: &mut NodeAdditions) {
    current_node.set_link(Some(link));
    node_additions.link = true;
}

fn add_node_with_hint(current_node: &mut Node, new_node: Node, node_additions: &mut NodeAdditions, hint: NodeHint) {
    match hint {
        NodeHint::Left => { add_node_left(current_node, new_node, node_additions); }
        NodeHint::Right => { add_node_right(current_node, new_node, node_additions); }
        NodeHint::Link => { add_node_link(current_node, new_node, node_additions); }
    }
}

fn take_node_with_hint(node: &mut Node, hint: NodeHint) -> Option<Box<Node>> {
    match hint {
        NodeHint::Left => { node.take_left() }
        NodeHint::Right => { node.take_right() }
        NodeHint::Link => { node.take_link() }
    }
}

fn borrow_node_with_hint(node: &mut Node, hint: NodeHint) -> Option<&mut Node> {
    match hint {
        NodeHint::Left => { node.borrow_left_mut() }
        NodeHint::Right => { node.borrow_right_mut() }
        NodeHint::Link => { node.borrow_link_mut() }
    }
}

struct NodeAdditions {
    left: bool,
    right: bool,
    link: bool,
}

impl NodeAdditions {
    pub fn new() -> Self {
        Self {
            left: false,
            right: false,
            link: false
        }
    }

    pub fn mark_with_hint(&mut self, node_hint: NodeHint) {
        match node_hint {
            NodeHint::Left => { self.left = true; }
            NodeHint::Right => { self.right = true; }
            NodeHint::Link => { self.link = true; }
        }
    }
}

#[derive(Copy, Clone)]
enum NodeHint {
    Left,
    Right,
    Link,
}