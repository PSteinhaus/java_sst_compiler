use std::borrow::BorrowMut;
use std::cell::{RefCell};
use std::rc::Rc;
use crate::parser::sym_table::{SymEntry, Type};

// TODO: create function that returns syntax tree in DOT format

pub struct Node {
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
    link: Option<Box<Node>>,

    node_type: SyntaxElement,

    return_val: Option<Type>,
    obj: Option<Rc<RefCell<SymEntry>>>,
}

impl Node {
    pub fn new(node_type: SyntaxElement, return_val: Option<Type>, obj: Option<Rc<RefCell<SymEntry>>>) -> Self {
        Self {
            left: None,
            right: None,
            link: None,
            node_type,
            return_val,
            obj,
        }
    }

    pub fn set_left(&mut self, node: Option<Node>) {
        self.left = if let Some(node) = node {
            Some(Box::new(node))
        } else {
            None
        };
    }
    pub fn set_right(&mut self, node: Option<Node>) {
        self.right = if let Some(node) = node {
            Some(Box::new(node))
        } else {
            None
        };
    }
    pub fn set_link(&mut self, node: Option<Node>) {
        self.link = if let Some(node) = node {
            Some(Box::new(node))
        } else {
            None
        };
    }
    pub fn set_left_boxed(&mut self, node: Box<Node>) {
        self.left = Some(node);
    }
    pub fn set_right_boxed(&mut self, node: Box<Node>) {
        self.right = Some(node);
    }
    pub fn set_link_boxed(&mut self, node: Box<Node>) {
        self.link = Some(node);
    }

    pub fn take_left(&mut self) -> Option<Box<Node>> {
        if self.left.is_some() {
            let boxed_node = std::mem::replace(&mut self.left, None);
            return Some(boxed_node.unwrap());
        }
        None
    }
    pub fn take_right(&mut self) -> Option<Box<Node>> {
        if self.right.is_some() {
            let boxed_node = std::mem::replace(&mut self.right, None);
            return Some(boxed_node.unwrap());
        }
        None
    }
    pub fn take_link(&mut self) -> Option<Box<Node>> {
        if self.link.is_some() {
            let boxed_node = std::mem::replace(&mut self.link, None);
            return Some(boxed_node.unwrap());
        }
        None
    }

    pub fn borrow_left_mut(&mut self) -> Option<&mut Node> {
        if let Some(boxed_node) = &mut self.left {
            return Some(boxed_node.borrow_mut());
        }
        None
    }
    pub fn borrow_right_mut(&mut self) -> Option<&mut Node> {
        if let Some(boxed_node) = &mut self.right {
            return Some(boxed_node.borrow_mut());
        }
        None
    }
    pub fn borrow_link_mut(&mut self) -> Option<&mut Node> {
        if let Some(boxed_node) = &mut self.link {
            return Some(boxed_node.borrow_mut());
        }
        None
    }

    pub fn node_type(&self) -> SyntaxElement {
        self.node_type
    }

    pub fn set_obj(&mut self, obj: Option<Rc<RefCell<SymEntry>>>) {
        self.obj = obj;
    }
    pub fn set_return_val(&mut self, val: Option<Type>) {
        self.return_val = val;
    }
}

#[derive(Debug, Copy, Clone)]
pub enum SyntaxElement {
    Class,
    Init,
    Enter,
    Call,
    Assign,
    /// A Var can be an identifier linked to a variable, but also an identifier linked to a constant.
    Var,
    /// A Const is a pure literal, with some direct value.
    Const,
    Binop(Binop),
    IfElse,
    If,
    While,
    Return
}

#[derive(Debug, Copy, Clone)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
    Equals,
    Smaller,
    SmallerEqual,
    Larger,
    LargerEqual,
}