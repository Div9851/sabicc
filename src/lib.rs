pub mod codegen;
pub mod parse;
pub mod tokenize;

use anyhow::{anyhow, Error};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone)]
pub enum ObjKind {
    Local(usize),
    Global(String),
    TypeDef,
}

#[derive(Clone)]
pub struct Obj {
    pub kind: ObjKind,
    pub ty: Rc<RefCell<Type>>,
}

impl Obj {
    fn is_global(&self) -> bool {
        matches!(self.kind, ObjKind::Global(_))
    }

    fn is_typedef(&self) -> bool {
        matches!(self.kind, ObjKind::TypeDef)
    }
}

#[derive(Debug)]
pub struct Member {
    pub offset: usize,
    pub ty: Rc<RefCell<Type>>,
}

#[derive(Debug, Clone)]
pub struct Decl {
    pub name: String,
    pub ty: Rc<RefCell<Type>>,
}

pub struct VarAttr {
    pub is_typedef: bool,
}

pub struct DeclSpec {
    pub ty: Rc<RefCell<Type>>,
    pub attr: VarAttr,
}

#[derive(Debug)]
pub enum TypeKind {
    Void,
    Char,
    Short,
    Int,
    Long,
    Ptr(Rc<RefCell<Type>>),
    Array(Rc<RefCell<Type>>, usize),
    Func {
        params: Vec<Decl>,
        return_ty: Rc<RefCell<Type>>,
    },
    Struct(HashMap<String, Member>),
    Union(HashMap<String, Member>),
}

#[derive(Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub size: Option<usize>, // sizeof() value
    pub align: usize,        // alignment
}

impl Type {
    fn new_void() -> Type {
        Type {
            kind: TypeKind::Void,
            size: None,
            align: 1,
        }
    }

    fn new_char() -> Type {
        Type {
            kind: TypeKind::Char,
            size: Some(1),
            align: 1,
        }
    }

    fn new_short() -> Type {
        Type {
            kind: TypeKind::Short,
            size: Some(2),
            align: 2,
        }
    }

    fn new_int() -> Type {
        Type {
            kind: TypeKind::Int,
            size: Some(4),
            align: 4,
        }
    }

    fn new_long() -> Type {
        Type {
            kind: TypeKind::Long,
            size: Some(8),
            align: 8,
        }
    }

    fn new_str(len: usize) -> Type {
        Type::new_array(&Type::new_char().wrap(), len)
    }

    fn new_ptr(base_ty: &Rc<RefCell<Type>>) -> Type {
        Type {
            kind: TypeKind::Ptr(Rc::clone(base_ty)),
            size: Some(8),
            align: 8,
        }
    }

    fn new_array(base_ty: &Rc<RefCell<Type>>, len: usize) -> Type {
        Type {
            kind: TypeKind::Array(Rc::clone(base_ty), len),
            size: Some(base_ty.borrow().size.unwrap() * len),
            align: base_ty.borrow().align,
        }
    }

    fn new_func(params: Vec<Decl>, return_ty: &Rc<RefCell<Type>>) -> Type {
        Type {
            kind: TypeKind::Func {
                params,
                return_ty: Rc::clone(return_ty),
            },
            size: None,
            align: 0,
        }
    }

    fn new_struct(member_decls: Vec<Decl>) -> Type {
        let mut members = HashMap::new();
        let mut offset = 0;
        let mut align = 1;
        for member_decl in member_decls {
            let member_size = member_decl.ty.borrow().size.unwrap();
            let member_align = member_decl.ty.borrow().align;
            offset = align_to(offset, align);
            members.insert(
                member_decl.name,
                Member {
                    offset,
                    ty: Rc::clone(&member_decl.ty),
                },
            );
            offset += member_size;
            if align < member_align {
                align = member_align;
            }
        }
        offset = align_to(offset, align);
        Type {
            kind: TypeKind::Struct(members),
            size: Some(offset),
            align,
        }
    }

    fn new_union(member_decls: Vec<Decl>) -> Type {
        let mut members = HashMap::new();
        let mut size = 0;
        let mut align = 1;
        for member_decl in member_decls {
            let member_size = member_decl.ty.borrow().size.unwrap();
            let member_align = member_decl.ty.borrow().align;
            members.insert(
                member_decl.name,
                Member {
                    offset: 0,
                    ty: Rc::clone(&member_decl.ty),
                },
            );
            if size < member_size {
                size = member_size;
            }
            if align < member_align {
                align = member_align;
            }
        }
        size = align_to(size, align);
        Type {
            kind: TypeKind::Union(members),
            size: Some(size),
            align,
        }
    }

    pub fn is_void(&self) -> bool {
        matches!(self.kind, TypeKind::Void)
    }

    pub fn is_integer(&self) -> bool {
        matches!(
            self.kind,
            TypeKind::Char | TypeKind::Short | TypeKind::Int | TypeKind::Long
        )
    }

    pub fn is_long(&self) -> bool {
        matches!(self.kind, TypeKind::Long)
    }

    pub fn is_ptr(&self) -> bool {
        matches!(self.kind, TypeKind::Ptr(_) | TypeKind::Array(_, _))
    }

    pub fn is_func(&self) -> bool {
        matches!(self.kind, TypeKind::Func { .. })
    }

    pub fn is_struct(&self) -> bool {
        matches!(self.kind, TypeKind::Struct(_))
    }

    pub fn is_union(&self) -> bool {
        matches!(self.kind, TypeKind::Union(_))
    }

    pub fn get_base_ty(&self) -> &Rc<RefCell<Type>> {
        match &self.kind {
            TypeKind::Ptr(base_ty) | TypeKind::Array(base_ty, _) => base_ty,
            _ => panic!("try to get base_ty of a non pointer type"),
        }
    }

    pub fn get_return_ty(&self) -> &Rc<RefCell<Type>> {
        match &self.kind {
            TypeKind::Func { return_ty, .. } => return_ty,
            _ => panic!("try to get return_ty of a non function type"),
        }
    }

    pub fn wrap(self) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(self))
    }
}

pub struct Context {
    pub text: String,
    pub filename: String,
    pub line_no: Vec<usize>,
    pub line_start_pos: Vec<usize>,
    pub line_end_pos: Vec<usize>,
    pub scopes: Vec<HashMap<String, Obj>>,
    pub tag_scopes: Vec<HashMap<String, Rc<RefCell<Type>>>>,
    pub init_data: HashMap<String, Vec<u8>>,
    pub id: usize,
    pub stack_size: usize,
}

impl Context {
    pub fn new(text: String, filename: String) -> Context {
        let mut line_no = vec![0; text.len()];
        let mut line_start_pos = Vec::new();
        let mut line_end_pos = Vec::new();
        let mut cur_line_no = 0;
        for (pos, ch) in text.bytes().enumerate() {
            line_no[pos] = cur_line_no;
            if line_start_pos.len() <= cur_line_no {
                line_start_pos.push(pos);
            }
            if ch == b'\n' {
                line_end_pos.push(pos);
                cur_line_no += 1;
            }
        }
        line_end_pos.push(text.len());
        Context {
            text,
            filename,
            line_no,
            line_start_pos,
            line_end_pos,
            scopes: Vec::new(),
            tag_scopes: Vec::new(),
            init_data: HashMap::new(),
            id: 0,
            stack_size: 0,
        }
    }

    pub fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.tag_scopes.push(HashMap::new());
    }

    pub fn leave_scope(&mut self) {
        self.scopes.pop();
        self.tag_scopes.pop();
    }

    pub fn new_lvar(&mut self, decl: &Decl) -> Obj {
        self.stack_size += decl.ty.borrow().size.unwrap();
        self.stack_size = align_to(self.stack_size, decl.ty.borrow().align);
        let offset = self.stack_size;
        let obj = Obj {
            kind: ObjKind::Local(offset),
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

    fn new_typedef(&mut self, decl: &Decl) -> Obj {
        let obj = Obj {
            kind: ObjKind::TypeDef,
            ty: Rc::clone(&decl.ty),
        };
        self.scopes
            .last_mut()
            .unwrap()
            .insert(decl.name.clone(), obj.clone());
        obj
    }

    fn new_tag(&mut self, tag: &str, ty: &Rc<RefCell<Type>>) {
        self.tag_scopes
            .last_mut()
            .unwrap()
            .insert(tag.to_owned(), Rc::clone(ty));
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
            ty: Type::new_str(bytes.len() + 1).wrap(),
        };
        let obj = self.new_gvar(&decl);
        self.init_data.insert(name, bytes);
        obj
    }

    pub fn find_var(&self, name: &str) -> Option<Obj> {
        for scope in self.scopes.iter().rev() {
            if let Some(obj) = scope.get(name) {
                return Some(obj.clone());
            }
        }
        None
    }

    pub fn find_tag(&self, tag: &str) -> Option<Rc<RefCell<Type>>> {
        for tag_scope in self.tag_scopes.iter().rev() {
            if let Some(ty) = tag_scope.get(tag) {
                return Some(Rc::clone(ty));
            }
        }
        None
    }

    pub fn find_tag_in_current_scope(&self, tag: &str) -> Option<Rc<RefCell<Type>>> {
        if let Some(ty) = self.tag_scopes.last().unwrap().get(tag) {
            Some(Rc::clone(ty))
        } else {
            None
        }
    }
}

//
// foo.c:10: x = y + 1;
//               ^ <error message here>
fn error_message(msg: &str, ctx: &Context, pos: usize) -> Error {
    let filename = &ctx.filename;
    let line_no = ctx.line_no[pos];
    let line_start_pos = ctx.line_start_pos[line_no];
    let line_end_pos = ctx.line_end_pos[line_no];
    let error_at = format!("{}:{}: ", filename, line_no + 1);
    let indent = error_at.len() + pos - line_start_pos;
    anyhow!(
        "\n{}{}\n{}^ {}",
        error_at,
        &ctx.text[line_start_pos..line_end_pos],
        " ".repeat(indent),
        msg
    )
}

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to(5, 8) returns 8 and align_to(11, 8) returns 16.
fn align_to(n: usize, align: usize) -> usize {
    (n + align - 1) / align * align
}
