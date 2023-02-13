pub mod codegen;
pub mod parse;
pub mod tokenize;

use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone)]
pub enum ObjKind {
    Local(usize),   // Offset from RBP
    Global(String), // label
}

#[derive(Clone)]
pub struct Obj {
    pub kind: ObjKind,
    pub ty: Rc<Type>,
}

#[derive(Clone)]
pub struct Decl {
    pub name: String,
    pub ty: Rc<Type>,
}

pub enum TypeKind {
    Int,
    Char,
    Ptr(Rc<Type>),
    Array(Rc<Type>, usize),
    Func {
        params: Vec<Decl>,
        return_ty: Rc<Type>,
    },
}

pub struct Type {
    pub kind: TypeKind,
    pub size: usize,
}

impl Type {
    fn new_int() -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Int,
            size: 8,
        })
    }
    fn new_char() -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Char,
            size: 1,
        })
    }
    fn new_str(len: usize) -> Rc<Type> {
        Type::new_array(&Type::new_char(), len)
    }
    fn new_ptr(base_ty: &Rc<Type>) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Ptr(Rc::clone(base_ty)),
            size: 8,
        })
    }
    fn new_array(base_ty: &Rc<Type>, len: usize) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Array(Rc::clone(base_ty), len),
            size: base_ty.size * len,
        })
    }
    fn new_func(params: Vec<Decl>, return_ty: &Rc<Type>) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Func {
                params,
                return_ty: Rc::clone(return_ty),
            },
            size: 0,
        })
    }
    pub fn is_integer(&self) -> bool {
        matches!(self.kind, TypeKind::Int | TypeKind::Char)
    }
    pub fn is_ptr(&self) -> bool {
        matches!(self.kind, TypeKind::Ptr(_) | TypeKind::Array(_, _))
    }
    pub fn is_func(&self) -> bool {
        matches!(
            self.kind,
            TypeKind::Func {
                params: _,
                return_ty: _
            }
        )
    }
    pub fn get_base_ty(&self) -> &Rc<Type> {
        match &self.kind {
            TypeKind::Ptr(base_ty) | TypeKind::Array(base_ty, _) => base_ty,
            _ => panic!("try to get base_ty of a non pointer type"),
        }
    }
}

pub struct Context {
    pub text: String,
    pub scopes: Vec<HashMap<String, Obj>>,
    pub init_data: HashMap<String, Vec<u8>>,
    pub id: usize,
    pub stack_size: usize,
}

impl Context {
    pub fn new(text: String) -> Context {
        Context {
            text,
            scopes: Vec::new(),
            init_data: HashMap::new(),
            id: 0,
            stack_size: 0,
        }
    }
    pub fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }
    pub fn leave_scope(&mut self) {
        self.scopes.pop();
    }
    pub fn new_lvar(&mut self, decl: &Decl) -> Obj {
        self.stack_size += decl.ty.size;
        let obj = Obj {
            kind: ObjKind::Local(self.stack_size),
            ty: Rc::clone(&decl.ty),
        };
        self.scopes
            .last_mut()
            .unwrap()
            .insert(decl.name.clone(), obj.clone());
        obj
    }
    fn new_gvar(&mut self, decl: &Decl) -> Obj {
        let obj = Obj {
            kind: ObjKind::Global(decl.name.clone()),
            ty: Rc::clone(&decl.ty),
        };
        self.scopes
            .first_mut()
            .unwrap()
            .insert(decl.name.clone(), obj.clone());
        obj
    }
    fn new_unique_name(&mut self) -> String {
        let name = format!(".L..{}", self.id);
        self.id += 1;
        name
    }
    fn new_str(&mut self, bytes: Vec<u8>) -> Obj {
        let name = self.new_unique_name();
        let decl = Decl {
            name: name.clone(),
            ty: Type::new_str(bytes.len() + 1),
        };
        let obj = self.new_gvar(&decl);
        self.init_data.insert(name, bytes);
        obj
    }
    pub fn find_var(&mut self, name: &str) -> Option<Obj> {
        for scope in self.scopes.iter().rev() {
            if let Some(obj) = scope.get(name) {
                return Some(obj.clone());
            }
        }
        None
    }
}

fn error_message(msg: &str, ctx: &Context, loc: usize) -> String {
    format!("\n{}{}^ {}", ctx.text, " ".repeat(loc), msg)
}
