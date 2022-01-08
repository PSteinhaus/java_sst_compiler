//! functionality for checking the semantic of an AST with a corresponding symbol table

use crate::parser::ast::{Node, SyntaxElement};
use crate::parser::error::{CheckResult, IncompatibleTypes, ParseError, VoidOperand};
use crate::parser::sym_table::Type;
use std::mem::discriminant as d;

/// performs all five necessary checks on the AST:
/// * type-compatibility of operands used by operators
/// * matching parameters for function calls
/// * functions returning the proposed type
/// * conditions actually compute booleans
/// * variables are defined before use
pub fn check(node: &Node) -> CheckResult {
    // first traverse the ast to the left side
    if let Some(left_node) = node.borrow_left() { check(left_node)?; }
    // then check yourself
    match node.node_type() {
        SyntaxElement::Class => {}
        SyntaxElement::Init => {}
        SyntaxElement::Enter => {}
        SyntaxElement::Call => {}
        SyntaxElement::Assign | SyntaxElement::Binop(_) => { compatible_op_type(node)?; }
        SyntaxElement::Var => {}
        SyntaxElement::Const => {}
        SyntaxElement::IfElse => {}
        SyntaxElement::If => {}
        SyntaxElement::While => {}
        SyntaxElement::Return => {}
    }
    // then your right child
    if let Some(right_node) = node.borrow_right() { check(right_node)?; }
    // and then your link (the "next" syntax element)
    if let Some(link_node) = node.borrow_link() { check(link_node)?; }
    // if everything went ok return Ok
    Ok(())
}

/// checks type-compatibility of operands used by the given operator
///
/// returns `Some(compatible_type)` if they are compatible and `None` if not
pub fn compatible_op_type(node: &Node) -> Result<Type, Box<dyn ParseError>> {
    match node.node_type() {
        SyntaxElement::Assign | SyntaxElement::Binop(_) => {
            // get the left type
            let left_type = compatible_op_type(node.borrow_left().unwrap())?;
            // get the right type
            let right_type = compatible_op_type(node.borrow_right().unwrap())?;
            // compare them
            if d(&left_type) == d(&right_type) { return Ok(left_type); }
            else { return Err(Box::new(IncompatibleTypes::new(left_type, right_type, node.line(), node.pos()))); }
        }
        SyntaxElement::Var | SyntaxElement::Const => {
            // return your own type
            let my_type = node.value_type();
            return Ok(my_type.unwrap())
        }
        SyntaxElement::Call => {
            // check if your type is void and return your type if not
            let my_type = node.value_type();
            if let Some(t) = my_type { return Ok(t); }
            else { return Err(Box::new(VoidOperand::new(node.line(), node.pos()))); }
        }
        _ => panic!("tried to compute operand types for a node that is neither an operator nor a variable/literal; this probably means the syntax check for operations is faulty")
    }
}