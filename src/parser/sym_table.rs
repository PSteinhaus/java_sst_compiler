use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::{Rc, Weak};
use crate::parser::error::{DoubleDeclaration, ParseError};
use crate::SSTint;

#[derive(Debug)]
pub struct SymTable {
    entries: HashMap<String, Rc<RefCell<SymEntry>>>,
    enclose: Option<Weak<RefCell<SymTable>>>,
    block_counter: usize,
}

impl SymTable {
    pub fn new(enclose: Option<Weak<RefCell<SymTable>>>) -> Self {
        Self {
            entries: HashMap::new(),
            enclose,
            block_counter: 0,
        }
    }

    pub fn get_entry(&self, name: &str) -> Option<Rc<RefCell<SymEntry>>> {
        if let Some(entry) = self.entries.get(name) {
            return Some(entry.clone());
        } else if let Some(weak_table) = &self.enclose {
            if let Some(table) = weak_table.upgrade() {
                return table.borrow().get_entry(name);
            }
            //let table_ptr = weak_table.as_ptr();
            //unsafe {
                // safe as long as the enclosing table will always live at least as long as this table (should be always)
                //if let Some(entry_ref) = (*table_ptr).borrow_mut().get_entry(name) {
                //    return Some(&*(entry_ref as *const SymEntry) as & 'static SymEntry);
                //}
            //}
        }
        None
    }

    /// Tries to add the entry to the table and returns an error if there already was one
    /// with the same name before
    pub fn add_entry(&mut self, entry: Rc<RefCell<SymEntry>>) -> Result<(), Box<dyn ParseError>> {
        let name = entry.borrow().name.clone();
        if let Some(other_entry) = self.entries.insert(name, entry) {
            let other_name = other_entry.borrow().name.clone();
            self.entries.insert(other_name.clone(), other_entry); // put it back in
            return Err(Box::new(DoubleDeclaration::new(other_name)))
        }
        Ok(())
    }

    pub fn remove_entry(&mut self, name: &str) -> Option<Rc<RefCell<SymEntry>>> {
        self.entries.remove(name)
    }

    pub fn enclose(&self) -> Option<Rc<RefCell<SymTable>>> {
        if let Some(enclose) = &self.enclose {
            return enclose.upgrade();
        }
        None
    }

    /// Adds a new block to the sym table and returns the sym table of that new block
    pub fn add_block(&mut self, self_directed_weak: Weak<RefCell<SymTable>>) -> Result<(Rc<RefCell<SymTable>>, String), Box<dyn ParseError>> {
        let block_sym_table = Rc::new(RefCell::new(SymTable::new(Some(self_directed_weak))));
        let block_name = self.block_counter.to_string();
        let new_block = Rc::new(RefCell::new(SymEntry::new(block_name.clone(), EntryType::Block(block_sym_table.clone()))));
        if let Err(e) = self.add_entry(new_block) {
            return Err(e);
        }
        // increment the block counter
        self.block_counter += 1;
        Ok((block_sym_table, block_name))
    }
}

#[derive(Debug)]
pub enum EntryType {
    Class(Rc<RefCell<SymTable>>),
    Var(Type),
    Const(Type),
    Proc(Rc<RefCell<SymTable>>, Vec<(Type, String)>, ResultType),
    Block(Rc<RefCell<SymTable>>),
    /// This variant is meant as a placeholder for use in AST nodes that weren't able to find a
    /// certain function name which might have only been defined later.
    ///
    /// It contains the symtable in which the function would need to have been defined
    Unresolved(Weak<RefCell<SymTable>>),
}

#[derive(Debug, Copy, Clone)]
pub enum ResultType {
    Int,
    Void,
}

#[derive(Debug, Copy, Clone)]
pub enum Type {
    Int(SSTint),
}

#[derive(Debug)]
pub struct SymEntry {
    name: String,
    entry_type: EntryType,
}

impl SymEntry {
    pub fn new(name: String, entry_type: EntryType) -> Self {
        Self { name, entry_type }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn entry_type(&self) -> &EntryType {
        &self.entry_type
    }

    /// Returns the integer value iff this entry is a variable or a constant.
    pub fn int_value(&self) -> Option<SSTint> {
        match self.entry_type {
            EntryType::Var(Type::Int(i)) | EntryType::Const(Type::Int(i)) => Some(i),
            _ => None,
        }
    }

    /// Returns a symbol table defining the parameters iff this entry is a procedure.
    pub fn params(&self) -> Option<&[(Type, String)]> {
        if let EntryType::Proc(_, p_list, _) = &self.entry_type {
            return Some(p_list);
        }
        None
    }

    /// Returns the return type iff the entry is a procedure.
    pub fn result_type(&self) -> Option<ResultType> {
        if let EntryType::Proc(_, _, res_t) = self.entry_type {
            return Some(res_t);
        }
        None
    }

    /// Returns a reference to the symbol table held by this entry.
    pub fn sym_table(&self) -> Option<Rc<RefCell<SymTable>>> {
        match self.entry_type() {
            EntryType::Class(table) | EntryType::Block(table) | EntryType::Proc(table, ..) => Some(table.clone()),
            _ => None,
        }
    }
}
