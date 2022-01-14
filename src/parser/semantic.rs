//! functionality for checking the semantic of an AST with a corresponding symbol table

use std::borrow::Borrow;
use std::cell::Ref;
use std::collections::HashSet;
use crate::parser::ast::{Node, SyntaxElement};
use crate::parser::error::{ArgumentMismatch, CheckResult, IncompatibleTypes, ParseError, UninitializedVar, VoidOperand, WrongOperandType, WrongReturnType};
use crate::parser::sym_table::{ResultType, SymEntry, Type};
use std::mem::discriminant as d;

pub fn check(node: &Node) -> CheckResult {
    let mut checker = SemChecker::new(node);
    checker.check(node)
}

struct SemChecker {
    initialized_vars: HashSet<String>
}

impl SemChecker {
    pub fn new(node: &Node) -> Self {
        // add the class variables to the list of initialized variables
        // (even though you can't be sure that they're really initialized, in fact they probably won't be)
        let mut initialized_vars = HashSet::new();
        let class_table = node.get_obj().as_ref().expect("tried to create SemChecker with something other than a class node").as_ref().borrow().sym_table().unwrap();
        for var_name in class_table.as_ref().borrow().var_names() {
            initialized_vars.insert(var_name);
        }
        Self {
            initialized_vars,
        }
    }

    /// performs all five necessary checks on the AST:
    /// * type-compatibility of operands used by operators (including assignment)
    /// * matching parameters for function calls
    /// * functions returning the proposed type on all execution paths
    /// * conditions actually compute booleans
    /// * variables are initialized before use
    fn check(&mut self, node: &Node) -> CheckResult {
        // first traverse the ast to the left side
        if let Some(left_node) = node.borrow_left() { self.check(left_node)?; }
        // then check yourself
        match node.node_type() {
            SyntaxElement::Class => {}
            SyntaxElement::Init => {}
            SyntaxElement::Enter => {
                check_return(node)?;
                self.check_initialization(node)?;
            }
            SyntaxElement::Call => { check_arguments(node)?; }
            SyntaxElement::Assign | SyntaxElement::Binop(_) => { compatible_op_type(node)?; }
            SyntaxElement::Var => {}
            SyntaxElement::Const => {}
            SyntaxElement::IfElse => {}
            SyntaxElement::If | SyntaxElement::While => {
                // check whether the left child (the condition) actually computes a boolean
                if let SyntaxElement::Binop(op) = node.borrow_left().expect("parser accepted if/while without condition").node_type() {
                    let v_type = op.value_type();
                    if let Type::Bool(_) = v_type {} else {
                        return Err(Box::new(WrongOperandType::new(node.line(), node.pos(), v_type, node.node_type())))
                    }
                }
            }
            SyntaxElement::Return => {}
        }
        // then your right child
        if let Some(right_node) = node.borrow_right() { self.check(right_node)?; }
        // and then your link (the "next" syntax element)
        if let Some(link_node) = node.borrow_link() { self.check(link_node)?; }
        // if everything went ok return Ok
        Ok(())
    }

    /// checks whether all variables used are initialized when they're used
    pub fn check_initialization(&self, node: &Node) -> CheckResult {
        /// go through all statements in this sequence and check the used vars for initialization until you either find a `return`,
        /// a `while` (in which case you treat it as a sub-sequence and check that),
        /// or a branch (if-else, in which case you recursively check both paths)
        fn check_execution_path(start_node: &Node, mut initialized_vars: HashSet<String>) -> CheckResult {
            let mut c_node = Some(start_node);
            while let Some(current_node) = c_node {
                match current_node.node_type() {
                    SyntaxElement::Const => {
                        // uninteresting to this analysis, just skip
                    }
                    SyntaxElement::Var => {
                        // this is the defining check: check whether this var has already been initialized
                        let name = current_node.get_obj().as_ref().unwrap().as_ref().borrow().name().to_string();
                        if !initialized_vars.contains(&name) {
                            return Err(Box::new(UninitializedVar::new(current_node.line(), current_node.pos(), name)));
                        }
                    }
                    SyntaxElement::Assign => {
                        // the var that this assign assigns to is now definitely initialized
                        initialized_vars.insert(current_node.borrow_left().expect("parser accepted assign without left side").get_obj().as_ref().unwrap().as_ref().borrow().name().to_string());
                    }
                    SyntaxElement::If | SyntaxElement::IfElse | SyntaxElement::Binop(_) | SyntaxElement::While => {
                        // call recursively on the children to check both execution paths
                        check_execution_path(current_node.borrow_left().unwrap(), initialized_vars.clone())?;
                        check_execution_path(current_node.borrow_right().unwrap(), initialized_vars.clone())?;
                    }
                    SyntaxElement::Call => {
                        // check the arguments given, which are stored in the left child (if there are arguments)
                        if let Some(arguments) = current_node.borrow_left() {
                            check_execution_path(arguments, initialized_vars.clone())?;
                        }
                    }
                    SyntaxElement::Return => {
                        // check the returned expression, which is the right child (if there is one)
                        if let Some(return_expression) = current_node.borrow_right() {
                            check_execution_path(return_expression, initialized_vars.clone())?;
                        }
                    }
                    _ => panic!("a node of a wrong type ({:?}) is part of this function", current_node.node_type())
                }
                // proceed onto the next statement
                c_node = current_node.borrow_link();
            }
            Ok(())
        }

        let mut init_vars = self.initialized_vars.clone();
        // first add all given arguments to the initialized vars
        let proc_entry: Ref<SymEntry> = node.get_obj().as_ref().expect("call has no sym table entry").as_ref().borrow();
        for param in proc_entry.params().unwrap() {
            init_vars.insert(param.1.clone());
        }
        check_execution_path(node.borrow_right().unwrap(), init_vars)
    }
}

/// checks type-compatibility of operands used by the given operator;
/// also checks whether the given types can be used with the operator at all;
///
/// returns `Some(compatible_type)` if they are compatible and `None` if not
pub fn compatible_op_type(node: &Node) -> Result<Type, Box<dyn ParseError>> {
    match node.node_type() {
        SyntaxElement::Assign => {
            // get the left type
            let left_type = compatible_op_type(node.borrow_left().unwrap())?;
            // get the right type
            let right_type = compatible_op_type(node.borrow_right().unwrap())?;
            // compare them
            if d(&left_type) == d(&right_type) {
                Ok(left_type)
            }
            else { return Err(Box::new(IncompatibleTypes::new(left_type, right_type, node.line(), node.pos()))); }
        }
        SyntaxElement::Binop(_) => {
            // get the left type
            let left_type = compatible_op_type(node.borrow_left().unwrap())?;
            // get the right type
            let right_type = compatible_op_type(node.borrow_right().unwrap())?;
            // compare them
            if d(&left_type) == d(&right_type) {
                // check whether the type of the operands is actually what the operator asked for (i.e. an int at this point)
                return if let Type::Int(_) = left_type {
                    Ok(left_type)
                } else {
                    Err(Box::new(WrongOperandType::new(node.line(), node.pos(), left_type, node.node_type())))
                };
            }
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
            return if let Some(t) = my_type { Ok(t) } else { Err(Box::new(VoidOperand::new(node.line(), node.pos()))) }
        }
        _ => panic!("tried to compute operand types for a node that is neither an operator nor a variable/literal; this probably means the syntax check for operations is faulty")
    }
}

/// checks whether the arguments given match the expected parameters
pub fn check_arguments(node: &Node) -> CheckResult {
    let proc_entry: Ref<SymEntry> = node.get_obj().as_ref().expect("call has no sym table entry").as_ref().borrow();
    let parameters = proc_entry.params().expect("parameters were not set");
    // the arguments are the left child and its links
    let mut argument = node.borrow_left();
    for p in parameters {
        // check whether there is another argument
        if let Some(argument_node) = argument {
            // check whether the type matches
            if d(&p.0) != d(&argument_node.value_type().expect("faulty parse accepted argument without value type")) {
                // argument with wrong type found
                return Err(Box::new(ArgumentMismatch::new(node.line(), node.pos())));
            }
            // prepare the next argument
            argument = argument_node.borrow_link();
        } else {
            // no argument found, though another parameter is expected
            return Err(Box::new(ArgumentMismatch::new(node.line(), node.pos())));
        }
    }
    // after going through all the links `argument` should be `None` now
    // if it isn't then there are more arguments than parameters
    if argument.is_some() { return Err(Box::new(ArgumentMismatch::new(node.line(), node.pos()))); }
    Ok(())
}

/// checks whether the function entered through this node returns the specified type on all execution paths
pub fn check_return(node: &Node) -> CheckResult {
    let proc_entry: Ref<SymEntry> = node.get_obj().as_ref().expect("call has no sym table entry").as_ref().borrow();
    let return_type = proc_entry.result_type().expect("procedure has no return type");

    // if the return type is `void` then just return Ok, as performing an analysis on whether this function
    // actually ever returns is the definition of solving the halting problem
    if let ResultType::Void = return_type { return Ok(()); }
    // so from now on we don't have to cover the void case anymore
    let return_type = return_type.to_type().unwrap();

    /// go through all statements in this sequence until you either find a `return`,
    /// or a branch (if-else, in which case you recursively check both paths for a return of the ret_type)
    fn check_execution_path(start_node: &Node, ret_type: Type) -> bool {
        let mut c_node = Some(start_node);
        while let Some(current_node) = c_node {
            match current_node.node_type() {
                SyntaxElement::Assign | SyntaxElement::Var | SyntaxElement::Const | SyntaxElement::Binop(_) | SyntaxElement::Call | SyntaxElement::While => {
                    // uninteresting to this analysis, just skip
                    // also skip while, as we can't be sure that it will execute
                }
                SyntaxElement::IfElse => {
                    // call recursively on the children to check both execution paths
                    // both paths have to return the specified type for the check to go through
                    let always_returns = check_execution_path(current_node.borrow_left().expect("parser accepted IfElse without If"), ret_type)
                        && check_execution_path(current_node.borrow_right().expect("parser accepted IfElse without Else"), ret_type);
                    if always_returns { return true; }
                }
                SyntaxElement::If => {
                    // look at the right child, as the left child is just the condition
                    if check_execution_path(current_node.borrow_right().unwrap(), ret_type) {
                        return true;
                    }
                }
                SyntaxElement::Return => {
                    // you've hit a `return`! check whether it's of the right type, by getting the type of its right child (if there is one)
                    let ret_value = current_node.borrow_right();
                    if let Some(value_node) = ret_value {
                        match value_node.node_type() {
                            SyntaxElement::Call | SyntaxElement::Var | SyntaxElement::Const => {
                                if d(&value_node.value_type().unwrap()) == d(&ret_type) {
                                    return true;
                                }
                            }
                            SyntaxElement::Binop(op) => {
                                if d(&op.value_type()) == d(&ret_type) {
                                    return true;
                                }
                            }
                            _ => panic!("nonsensical node after return")
                        }
                    }
                    // if execution proceeds to here, then the return had the wrong type or no type at all (void), which we excluded already
                    return false;
                }
                _ => panic!("a node of a wrong type ({:?}) is part of this function", current_node.node_type())
            }
            // proceed onto the next statement
            c_node = current_node.borrow_link();
        }
        false
    }

    // check on the right child (the first statement), which can be unwrapped, as the language
    // specification states that there always needs to be at least one statement in a function
    if check_execution_path(node.borrow_right().unwrap(), return_type) {
        Ok(())
    } else {
        Err(Box::new(WrongReturnType::new(node.line(), node.pos(), return_type)))
    }
}