pub mod codegen;
pub mod parse;
pub mod tokenize;

use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone)]
pub enum ObjKind {
    Local(usize),   // offset from RBP
    Global(String), // label
}

#[derive(Clone)]
pub struct Obj {
    pub kind: ObjKind,
    pub ty: Rc<Type>,
}

pub struct Member {
    pub offset: usize,
    pub ty: Rc<Type>,
}

#[derive(Clone)]
pub struct Decl {
    pub name: String,
    pub ty: Rc<Type>,
}

pub enum TypeKind {
    Char,
    Short,
    Int,
    Long,
    Ptr(Rc<Type>),
    Array(Rc<Type>, usize),
    Func {
        params: Vec<Decl>,
        return_ty: Rc<Type>,
    },
    Struct(HashMap<String, Member>),
    Union(HashMap<String, Member>),
}

pub struct Type {
    pub kind: TypeKind,
    pub size: usize,  // sizeof() value
    pub align: usize, // alignment
}

impl Type {
    fn new_char() -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Char,
            size: 1,
            align: 1,
        })
    }

    fn new_short() -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Short,
            size: 2,
            align: 2,
        })
    }

    fn new_int() -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Int,
            size: 4,
            align: 4,
        })
    }

    fn new_long() -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Char,
            size: 8,
            align: 8,
        })
    }

    fn new_str(len: usize) -> Rc<Type> {
        Type::new_array(&Type::new_char(), len)
    }

    fn new_ptr(base_ty: &Rc<Type>) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Ptr(Rc::clone(base_ty)),
            size: 8,
            align: 8,
        })
    }

    fn new_array(base_ty: &Rc<Type>, len: usize) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Array(Rc::clone(base_ty), len),
            size: base_ty.size * len,
            align: base_ty.align,
        })
    }

    fn new_func(params: Vec<Decl>, return_ty: &Rc<Type>) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Func {
                params,
                return_ty: Rc::clone(return_ty),
            },
            size: 0,
            align: 0,
        })
    }

    fn new_struct(member_decls: Vec<Decl>) -> Rc<Type> {
        let mut members = HashMap::new();
        let mut offset = 0;
        let mut align = 1;
        for member_decl in member_decls {
            let member_size = member_decl.ty.size;
            let member_align = member_decl.ty.align;
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
        Rc::new(Type {
            kind: TypeKind::Struct(members),
            size: align_to(offset, align),
            align,
        })
    }

    fn new_union(member_decls: Vec<Decl>) -> Rc<Type> {
        let mut members = HashMap::new();
        let mut size = 0;
        let mut align = 1;
        for member_decl in member_decls {
            let member_size = member_decl.ty.size;
            let member_align = member_decl.ty.align;
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
        Rc::new(Type {
            kind: TypeKind::Struct(members),
            size: align_to(size, align),
            align,
        })
    }

    pub fn is_integer(&self) -> bool {
        matches!(
            self.kind,
            TypeKind::Char | TypeKind::Short | TypeKind::Int | TypeKind::Long
        )
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

    pub fn is_struct(&self) -> bool {
        matches!(self.kind, TypeKind::Struct(_))
    }

    pub fn is_union(&self) -> bool {
        matches!(self.kind, TypeKind::Union(_))
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
    pub filename: String,
    pub line_no: Vec<usize>,
    pub line_start_pos: Vec<usize>,
    pub line_end_pos: Vec<usize>,
    pub scopes: Vec<HashMap<String, Obj>>,
    pub tag_scopes: Vec<HashMap<String, Rc<Type>>>,
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
        self.stack_size += decl.ty.size;
        self.stack_size = align_to(self.stack_size, decl.ty.align);
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
    fn new_tag(&mut self, tag: &str, ty: &Rc<Type>) {
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
    pub fn find_tag(&self, tag: &str) -> Option<Rc<Type>> {
        for tag_scope in self.tag_scopes.iter().rev() {
            if let Some(ty) = tag_scope.get(tag) {
                return Some(Rc::clone(ty));
            }
        }
        None
    }
}

//
// foo.c:10: x = y + 1;
//               ^ <error message here>
fn error_message(msg: &str, ctx: &Context, pos: usize) -> String {
    let filename = &ctx.filename;
    let line_no = ctx.line_no[pos];
    let line_start_pos = ctx.line_start_pos[line_no];
    let line_end_pos = ctx.line_end_pos[line_no];
    let info = format!("{}:{}: ", filename, line_no + 1);
    format!(
        "\n{}{}\n{}^ {}",
        info,
        &ctx.text[line_start_pos..line_end_pos],
        " ".repeat(info.len() + pos - line_start_pos),
        msg
    )
}

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to(5, 8) returns 8 and align_to(11, 8) returns 16.
fn align_to(n: usize, align: usize) -> usize {
    (n + align - 1) / align * align
}
