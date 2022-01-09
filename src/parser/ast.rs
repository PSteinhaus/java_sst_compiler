use std::borrow::{Borrow, BorrowMut};
use std::cell::{RefCell};
use std::ops::{Deref};
use std::rc::Rc;
use crate::input::{CPos, LNum};
use crate::parser::error::{ParseResult, UndefinedSymbol};
use crate::parser::sym_table::{EntryType, SymEntry, Type};

// TODO: create function that returns syntax tree in DOT format

pub struct Node {
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
    link: Option<Box<Node>>,

    node_type: SyntaxElement,

    return_val: Option<Type>,
    obj: Option<Rc<RefCell<SymEntry>>>,

    line: LNum,
    pos: CPos,
}

impl Node {
    pub fn new(node_type: SyntaxElement, return_val: Option<Type>, obj: Option<Rc<RefCell<SymEntry>>>, line: LNum, pos: CPos) -> Self {
        Self {
            left: None,
            right: None,
            link: None,
            node_type,
            return_val,
            obj,
            line,
            pos,
        }
    }

    pub fn line(&self) -> LNum { self.line }
    pub fn pos(&self) -> CPos { self.pos }

    pub fn has_children(&self) -> bool {
        self.left.is_some() || self.right.is_some()
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

    pub fn borrow_left(&self) -> Option<&Node> {
        if let Some(boxed_node) = &self.left {
            return Some(boxed_node.borrow());
        }
        None
    }
    pub fn borrow_right(&self) -> Option<&Node> {
        if let Some(boxed_node) = &self.right {
            return Some(boxed_node.borrow());
        }
        None
    }
    pub fn borrow_link(&self) -> Option<&Node> {
        if let Some(boxed_node) = &self.link {
            return Some(boxed_node.borrow());
        }
        None
    }

    pub fn node_type(&self) -> SyntaxElement {
        self.node_type
    }

    pub fn set_obj(&mut self, obj: Option<Rc<RefCell<SymEntry>>>) {
        self.obj = obj;
    }
    pub fn get_obj(&self) -> &Option<Rc<RefCell<SymEntry>>> { &self.obj }
    pub fn set_return_val(&mut self, val: Option<Type>) {
        self.return_val = val;
    }

    pub fn resolve_table_links(&mut self) -> ParseResult {
        if let Some(node) = &mut self.left { node.resolve_table_links()?; }

        if let Some(entry) = &self.obj {
            let sym_entry = entry.deref().borrow();
            if let EntryType::Unresolved(weak_table) = sym_entry.entry_type() {
                let table = weak_table.upgrade().expect("sym table was lost for some reason");
                let unresolved_name = sym_entry.name();
                let desired_entry_option = table.deref().borrow().get_entry(unresolved_name);
                if let Some(desired_entry) = desired_entry_option {
                    drop(sym_entry);
                    self.obj = Some(desired_entry);
                } else {
                    return Err(Box::new(UndefinedSymbol::new(unresolved_name.to_string())));
                }
            }
        }

        if let Some(node) = &mut self.right { node.resolve_table_links()?; }
        if let Some(node) = &mut self.link { node.resolve_table_links()?; }
        Ok(())
    }

    pub fn value_type(&self) -> Option<Type> {
        if let SyntaxElement::Const = self.node_type {
            return self.return_val;
        }
        if let Some(entry) = &self.obj {
            let sym_entry = entry.deref().borrow();
            return match sym_entry.entry_type() {
                EntryType::Var(t) => Some(*t),
                EntryType::Const(t) => Some(*t),
                EntryType::Proc(_, _, return_type) => return_type.to_type(),
                _ => None
            };
        }
        None
    }

    pub fn dot_representation(&self) -> String {
        let builder = DotBuilder::new();
        builder.start_with(&self)
    }

    fn dot_label(&self) -> String {
        if let Some(Type::Int(i)) = &self.return_val {
            return (*i).to_string();
        }
        let name = if let Some(entry) = &self.obj {
            entry.deref().borrow().name().to_string()
        } else {
            "".to_string()
        };

        match &self.node_type {
            SyntaxElement::Class => {
                format!("class {}", name)
            }
            SyntaxElement::Init => {
                format!("init")
            }
            SyntaxElement::Enter => {
                format!("enter {}()", name)
            }
            SyntaxElement::Call => {
                format!("call {}()", name)
            }
            SyntaxElement::Assign => {
                format!("assign")
            }
            SyntaxElement::Var => {
                format!("var {}", name)
            }
            SyntaxElement::Const => {
                panic!("consts should be literals and should be handled already by checking `return_val`");
            }
            SyntaxElement::Binop(b) => {
                format!("binop {:?}", *b)
            }
            SyntaxElement::IfElse => {
                format!("ifElse")
            }
            SyntaxElement::If => {
                format!("if")
            }
            SyntaxElement::While => {
                format!("while")
            }
            SyntaxElement::Return => {
                format!("return")
            }
        }
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

/// A helper struct to construct a DOT representation of the AST
pub struct DotBuilder {
    content: String,
    node_num: usize,
}

impl DotBuilder {
    pub fn new() -> Self {
        Self {
            content: "".to_string(),
            node_num: 0
        }
    }

    fn add_next_node_entry(&mut self, node: &Node) {
        let s = format!("{} [label=\"{}\"];\n", self.node_num, node.dot_label());
        self.node_num += 1;
        self.content.push_str(s.as_str());
    }

    fn add_empty_node_entry(&mut self) {
        let s = format!("{} [shape=point];\n", self.node_num);
        self.node_num += 1;
        self.content.push_str(s.as_str());
    }

    fn restrict_latest(&mut self) {
        let s = format!("{{ rank = same; {}; {}; }}\n", self.node_num - 2, self.node_num - 1);
        self.content.push_str(s.as_str());
    }

    fn connect(&mut self, id_start: usize, id_end: usize) {
        let s = format!("{} -> {};\n", id_start, id_end);
        self.content.push_str(s.as_str());
    }

    pub fn start_with(mut self, node: &Node) -> String {
        // first start the graph
        self.content.push_str("digraph {\n");
        // then add an entry for this node
        self.add_next_node_entry(node);
        // then add the rest
        self.add_node(node);
        // and finally end the graph
        self.content.push_str("}\n");

        self.content
    }

    fn latest_id(&self) -> usize { self.node_num - 1 }

    fn enforce_ordering(&mut self, left: usize, right: usize) {
        self.content.push_str(&*format!("{{\
rank = same;\
edge[style=invis];\
{} -> {};\
rankdir = LR;\
}}\n", left, right));
    }

    fn add_node(&mut self, node: &Node) {
        let own_id = self.latest_id();
        // add an entry for the link if there is one
        if let Some(link) = node.borrow_link() {
            self.add_next_node_entry(link);
            // now add an edge between them
            self.connect(own_id, self.latest_id());
            // and since there is one also add a rank restriction binding them to the same rank
            self.restrict_latest();
            // and now recursively add the linked node tree
            self.add_node(link);
        }
        // before adding the children check whether there are any at all (to avoid creating useless empty nodes)
        if node.has_children() {
            // now add left first
            let left_id;
            if let Some(left) = node.borrow_left() {
                self.add_next_node_entry(left);
                // now add an edge between them
                left_id = self.latest_id();
                self.connect(own_id, left_id);
                // and now recursively add the left node tree
                self.add_node(left);
            } else {
                self.add_empty_node_entry();
                left_id = self.latest_id();
                self.connect(own_id, left_id);
            }
            let right_id;
            // then right
            if let Some(right) = node.borrow_right() {
                self.add_next_node_entry(right);
                // now add an edge between them
                right_id = self.latest_id();
                self.connect(own_id, right_id);
                // and now recursively add the right node tree
                self.add_node(right);
            } else {
                self.add_empty_node_entry();
                right_id = self.latest_id();
                self.connect(own_id, right_id);
            }
            // finally enforce a left to right ordering through invisible edges
            self.enforce_ordering(left_id, right_id);
        }
    }
}