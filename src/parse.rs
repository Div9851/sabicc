use anyhow::Result;
use std::cell::RefCell;
use std::mem;
use std::rc::Rc;

use crate::tokenize::{self, Token};
use crate::{
    align_to, error_message, Context, Decl, DeclSpec, Obj, ObjKind, Type, TypeKind, VarAttr,
};

pub struct Program {
    pub funcs: Vec<Box<Func>>,
    pub ctx: Context,
}

impl Program {
    fn new(text: String, filename: String) -> Program {
        let funcs = Vec::new();
        let ctx = Context::new(text, filename);
        Program { funcs, ctx }
    }
}

pub struct Func {
    pub name: String,
    pub return_ty: Rc<RefCell<Type>>,
    pub params: Vec<Obj>,
    pub body: Box<Stmt>,
    pub stack_size: usize,
    pub is_static: bool,
}

#[derive(Debug)]
pub enum StmtKind {
    NullStmt,
    ReturnStmt(Box<Expr>),
    CompoundStmt(Vec<Box<Stmt>>),
    ExprStmt(Box<Expr>),
    SwitchStmt {
        cond: Box<Expr>,
        body: Box<Stmt>,
        case_labels: Vec<(i64, String)>,
        default_label: Option<String>,
        break_label: String,
    },
    IfStmt {
        cond: Box<Expr>,
        then: Box<Stmt>,
        els: Option<Box<Stmt>>,
    },
    ForStmt {
        init: Vec<Box<Stmt>>,
        cond: Option<Box<Expr>>,
        inc: Option<Box<Expr>>,
        body: Box<Stmt>,
        break_label: String,
        continue_label: String,
    },
    WhileStmt {
        cond: Box<Expr>,
        body: Box<Stmt>,
        break_label: String,
        continue_label: String,
    },
    LabeledStmt(String, Box<Stmt>),
    GotoStmt(String),
}

#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub loc: usize,
}

impl Stmt {
    fn get_body(self) -> Vec<Box<Stmt>> {
        if let StmtKind::CompoundStmt(body) = self.kind {
            body
        } else {
            panic!("expected a compound statement");
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BinaryOp {
    ADD,    // +
    SUB,    // -
    MUL,    // *
    DIV,    // /
    MOD,    // %
    BITAND, // &
    BITOR,  // |
    BITXOR, // ^
    LOGAND, // &&
    LOGOR,  // ||
    SHL,    // <<
    SHR,    // >>
    EQ,     // ==
    NE,     // !=
    LT,     // <
    LE,     // <=
}

#[derive(Clone, Copy, Debug)]
pub enum UnaryOp {
    NEG,    // -
    DEREF,  // *
    ADDR,   // &
    NOT,    // !
    BITNOT, // ~
}

#[derive(Debug)]
pub enum ExprKind {
    NullExpr,
    StmtExpr(Vec<Box<Stmt>>),
    Assign {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Comma {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Member {
        expr: Box<Expr>,
        offset: usize,
    },
    Var(Obj),
    Num(i64),
    FunCall {
        name: String,
        args: Vec<Box<Expr>>,
    },
    Cast(Box<Expr>),
    Cond {
        cond: Box<Expr>,
        then: Box<Expr>,
        els: Box<Expr>,
    },
    MemZero(Obj),
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Rc<RefCell<Type>>,
    pub loc: usize,
}

// This enum represents a variable initializer. Since initializers
// can be nested (e.g. `int x[2][2] = {{1, 2}, {3, 4}}`), this enum
// is a tree data structure.
#[derive(Debug)]
pub enum Initializer {
    Scalar(Box<Expr>),
    Compound(Vec<Box<Initializer>>),
}

impl Initializer {
    fn to_lvar_init(self, ty: &Rc<RefCell<Type>>, mut offset: usize, loc: usize) -> Box<Expr> {
        match self {
            Initializer::Compound(expr_vec) => {
                let ty = ty.borrow();
                let base_ty = ty.get_base_ty();
                let base_ty_size = base_ty.borrow().size.unwrap();
                let mut lhs = Expr::new_null(loc);
                for expr in expr_vec {
                    let rhs = expr.to_lvar_init(base_ty, offset, loc);
                    lhs = Expr::new_comma(lhs, rhs, loc);
                    offset -= base_ty_size;
                }
                lhs
            }
            Initializer::Scalar(expr) => {
                let obj = Obj {
                    kind: ObjKind::Local(offset),
                    ty: Rc::clone(&ty),
                };
                let var = Expr::new_var(obj, loc);
                Expr::new_assign(var, expr, loc)
            }
        }
    }
}

fn get_common_type(ty1: &Rc<RefCell<Type>>, ty2: &Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
    let ty1_size = ty1.borrow().size.unwrap();
    let ty2_size = ty2.borrow().size.unwrap();
    if ty1_size == 8 || ty2_size == 8 {
        Type::new_long().wrap()
    } else {
        Type::new_int().wrap()
    }
}

// For many binary operators, we implicitly promote operands so that
// both operands have the same type. Any integral type smaller than
// int is always promoted to int. If the type of one operand is larger
// than the other's (e.g. "long" vs. "int"), the smaller operand will
// be promoted to match with the other.
//
// This operation is called the "usual arithmetic conversion".
fn usual_arith_conv(lhs: Box<Expr>, rhs: Box<Expr>) -> (Box<Expr>, Box<Expr>) {
    let ty = get_common_type(&lhs.ty, &rhs.ty);
    let lhs_loc = lhs.loc;
    let rhs_loc = rhs.loc;
    (
        Expr::new_cast(lhs, &ty, lhs_loc),
        Expr::new_cast(rhs, &ty, rhs_loc),
    )
}

impl Expr {
    pub fn new_null(loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::NullExpr,
            ty: Type::new_void().wrap(),
            loc,
        })
    }
    pub fn new_assign(lhs: Box<Expr>, rhs: Box<Expr>, loc: usize) -> Box<Expr> {
        let result_ty = Rc::clone(&lhs.ty);
        let rhs = Expr::new_cast(rhs, &lhs.ty, loc);
        Box::new(Expr {
            kind: ExprKind::Assign { lhs, rhs },
            ty: result_ty,
            loc,
        })
    }

    // Convert `A op= B` to `tmp = &A, *tmp = *tmp op B`
    // where tmp is a fresh pointer variable.
    fn new_op_assign(
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        ctx: &mut Context,
        loc: usize,
    ) -> Result<Box<Expr>> {
        let var = ctx.new_lvar(&Decl {
            name: "".to_owned(),
            ty: Type::new_ptr(&lhs.ty).wrap(),
        });
        let expr1 = Expr::new_assign(
            Expr::new_var(var.clone(), loc),
            Expr::new_unary(UnaryOp::ADDR, lhs, ctx, loc)?,
            loc,
        );
        let expr2 = Expr::new_assign(
            Expr::new_unary(UnaryOp::DEREF, Expr::new_var(var.clone(), loc), ctx, loc)?,
            Expr::new_binary(
                op,
                Expr::new_unary(UnaryOp::DEREF, Expr::new_var(var.clone(), loc), ctx, loc)?,
                rhs,
                ctx,
                loc,
            )?,
            loc,
        );
        Ok(Expr::new_comma(expr1, expr2, loc))
    }

    // Convert A++ to `(typeof A)((A += 1) - 1)`
    fn new_inc_dec(
        expr: Box<Expr>,
        addend: i64,
        ctx: &mut Context,
        loc: usize,
    ) -> Result<Box<Expr>> {
        let ty = Rc::clone(&expr.ty);
        Ok(Expr::new_cast(
            Expr::new_add(
                Expr::new_op_assign(BinaryOp::ADD, expr, Expr::new_num(addend, loc), ctx, loc)?,
                Expr::new_num(-addend, loc),
                ctx,
                loc,
            )?,
            &ty,
            loc,
        ))
    }

    fn new_binary(
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        ctx: &Context,
        loc: usize,
    ) -> Result<Box<Expr>> {
        match op {
            BinaryOp::ADD => Expr::new_add(lhs, rhs, ctx, loc),
            BinaryOp::SUB => Expr::new_sub(lhs, rhs, ctx, loc),
            BinaryOp::MUL
            | BinaryOp::DIV
            | BinaryOp::MOD
            | BinaryOp::BITAND
            | BinaryOp::BITXOR
            | BinaryOp::BITOR => {
                if lhs.ty.borrow().is_integer() && rhs.ty.borrow().is_integer() {
                    let (lhs, rhs) = usual_arith_conv(lhs, rhs);
                    let ty = Rc::clone(&lhs.ty);
                    let expr = Expr {
                        kind: ExprKind::Binary { op, lhs, rhs },
                        ty,
                        loc,
                    };
                    Ok(Box::new(expr))
                } else {
                    Err(error_message("invalid operands", ctx, loc))
                }
            }
            BinaryOp::SHL | BinaryOp::SHR => {
                let ty = Rc::clone(&lhs.ty);
                let expr = Expr {
                    kind: ExprKind::Binary { op, lhs, rhs },
                    ty,
                    loc,
                };
                Ok(Box::new(expr))
            }
            BinaryOp::EQ
            | BinaryOp::NE
            | BinaryOp::LT
            | BinaryOp::LE
            | BinaryOp::LOGAND
            | BinaryOp::LOGOR => {
                let (lhs, rhs) = usual_arith_conv(lhs, rhs);
                let expr = Expr {
                    kind: ExprKind::Binary { op, lhs, rhs },
                    ty: Type::new_int().wrap(),
                    loc,
                };
                Ok(Box::new(expr))
            }
        }
    }

    fn new_add(
        mut lhs: Box<Expr>,
        mut rhs: Box<Expr>,
        ctx: &Context,
        loc: usize,
    ) -> Result<Box<Expr>> {
        if lhs.ty.borrow().is_integer() && rhs.ty.borrow().is_ptr() {
            mem::swap(&mut lhs, &mut rhs);
        }
        let result_ty;
        if lhs.ty.borrow().is_integer() && rhs.ty.borrow().is_integer() {
            // `integer + integer`
            (lhs, rhs) = usual_arith_conv(lhs, rhs);
            result_ty = Rc::clone(&lhs.ty);
        } else if lhs.ty.borrow().is_ptr() && rhs.ty.borrow().is_integer() {
            // `ptr + integer`
            let size = lhs.ty.borrow().get_base_ty().borrow().size;
            if size.is_none() {
                return Err(error_message("invalid operands", ctx, loc));
            }
            rhs = Expr::new_binary(
                BinaryOp::MUL,
                rhs,
                Expr::new_long(size.unwrap() as i64, loc),
                ctx,
                loc,
            )?;
            result_ty = Rc::clone(&lhs.ty);
        } else {
            return Err(error_message("invalid operands", ctx, loc));
        }
        Ok(Box::new(Expr {
            kind: ExprKind::Binary {
                op: BinaryOp::ADD,
                lhs,
                rhs,
            },
            ty: result_ty,
            loc,
        }))
    }

    fn new_sub(
        mut lhs: Box<Expr>,
        mut rhs: Box<Expr>,
        ctx: &Context,
        loc: usize,
    ) -> Result<Box<Expr>> {
        let result_ty;
        let mut div = 1;
        if lhs.ty.borrow().is_integer() && rhs.ty.borrow().is_integer() {
            // `integer - integer`
            (lhs, rhs) = usual_arith_conv(lhs, rhs);
            result_ty = Rc::clone(&lhs.ty);
        } else if lhs.ty.borrow().is_ptr() && rhs.ty.borrow().is_integer() {
            // `ptr - integer`
            let size = lhs.ty.borrow().get_base_ty().borrow().size;
            if size.is_none() {
                return Err(error_message("invalid operands", ctx, loc));
            }
            rhs = Expr::new_binary(
                BinaryOp::MUL,
                rhs,
                Expr::new_long(size.unwrap() as i64, loc),
                ctx,
                loc,
            )?;
            result_ty = Rc::clone(&lhs.ty);
        } else if lhs.ty.borrow().is_ptr() && rhs.ty.borrow().is_ptr() {
            // `ptr - ptr`
            let size = lhs.ty.borrow().get_base_ty().borrow().size;
            if size.is_none() {
                return Err(error_message("invalid operands", ctx, loc));
            }
            div = size.unwrap() as i64;
            result_ty = Type::new_int().wrap();
        } else {
            return Err(error_message("invalid operands", ctx, loc));
        }
        let mut expr = Box::new(Expr {
            kind: ExprKind::Binary {
                op: BinaryOp::SUB,
                lhs,
                rhs,
            },
            ty: result_ty,
            loc,
        });
        if div > 1 {
            expr = Expr::new_binary(BinaryOp::DIV, expr, Expr::new_num(div, loc), ctx, loc)?;
        }
        Ok(expr)
    }

    fn new_unary(op: UnaryOp, mut expr: Box<Expr>, ctx: &Context, loc: usize) -> Result<Box<Expr>> {
        let result_ty;
        match op {
            UnaryOp::NEG => {
                if expr.ty.borrow().is_integer() {
                    result_ty = get_common_type(&Type::new_int().wrap(), &expr.ty);
                    expr = Expr::new_cast(expr, &result_ty, loc);
                } else {
                    return Err(error_message("invalid operand", ctx, loc));
                }
            }
            UnaryOp::DEREF => {
                if expr.ty.borrow().is_ptr() {
                    let ty = expr.ty.borrow();
                    if ty.get_base_ty().borrow().is_void() {
                        return Err(error_message("dereferencing a void pointer", ctx, loc));
                    }
                    result_ty = Rc::clone(expr.ty.borrow().get_base_ty());
                } else {
                    return Err(error_message("invalid pointer dereference", ctx, loc));
                }
            }
            UnaryOp::ADDR => {
                if expr.ty.borrow().is_array() {
                    result_ty = Type::new_ptr(&expr.ty.borrow().get_base_ty()).wrap();
                } else {
                    result_ty = Type::new_ptr(&expr.ty).wrap();
                }
            }
            UnaryOp::NOT => {
                result_ty = Type::new_int().wrap();
            }
            UnaryOp::BITNOT => {
                result_ty = Rc::clone(&expr.ty);
            }
        }
        Ok(Box::new(Expr {
            kind: ExprKind::Unary { op, expr },
            ty: result_ty,
            loc,
        }))
    }

    fn new_comma(lhs: Box<Expr>, rhs: Box<Expr>, loc: usize) -> Box<Expr> {
        let ty = Rc::clone(&rhs.ty);
        let expr = Expr {
            kind: ExprKind::Comma { lhs, rhs },
            ty,
            loc,
        };
        Box::new(expr)
    }

    fn new_member(expr: Box<Expr>, name: &str, ctx: &Context, loc: usize) -> Result<Box<Expr>> {
        let offset;
        let ty;
        if let TypeKind::Struct(members) | TypeKind::Union(members) = &expr.ty.borrow().kind {
            if let Some(member) = members.get(name) {
                offset = member.offset;
                ty = Rc::clone(&member.ty);
            } else {
                return Err(error_message("no such member", ctx, loc));
            }
        } else {
            return Err(error_message("not struct nor union", ctx, expr.loc));
        }
        Ok(Box::new(Expr {
            kind: ExprKind::Member { expr, offset },
            ty,
            loc,
        }))
    }

    pub fn new_var(obj: Obj, loc: usize) -> Box<Expr> {
        let ty = Rc::clone(&obj.ty);
        Box::new(Expr {
            kind: ExprKind::Var(obj),
            ty,
            loc,
        })
    }

    fn new_num(val: i64, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Num(val),
            ty: Type::new_int().wrap(),
            loc,
        })
    }

    fn new_long(val: i64, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Num(val),
            ty: Type::new_long().wrap(),
            loc,
        })
    }

    fn new_funcall(
        name: &str,
        args: Vec<Box<Expr>>,
        return_ty: &Rc<RefCell<Type>>,
        loc: usize,
    ) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::FunCall {
                name: name.to_owned(),
                args,
            },
            ty: Rc::clone(&return_ty),
            loc,
        })
    }

    fn new_cast(expr: Box<Expr>, convert_to: &Rc<RefCell<Type>>, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Cast(expr),
            ty: Rc::clone(convert_to),
            loc,
        })
    }

    fn new_memzero(obj: Obj, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::MemZero(obj),
            ty: Type::new_void().wrap(),
            loc,
        })
    }
}

fn eval(expr: &Box<Expr>, ctx: &Context) -> Result<i64> {
    let err = Err(error_message("not a compile-time constant", ctx, expr.loc));
    match &expr.kind {
        ExprKind::Binary { op, lhs, rhs } => {
            let lhs = eval(lhs, ctx)?;
            let rhs = eval(rhs, ctx)?;
            match op {
                BinaryOp::ADD => Ok(lhs.wrapping_add(rhs)),
                BinaryOp::SUB => Ok(lhs.wrapping_sub(rhs)),
                BinaryOp::MUL => Ok(lhs.wrapping_mul(rhs)),
                BinaryOp::DIV => Ok(lhs.wrapping_div(rhs)),
                BinaryOp::MOD => Ok(lhs.wrapping_rem(rhs)),
                BinaryOp::BITAND => Ok(lhs & rhs),
                BinaryOp::BITOR => Ok(lhs | rhs),
                BinaryOp::BITXOR => Ok(lhs ^ rhs),
                BinaryOp::SHL => Ok(lhs.wrapping_shl(rhs as u32)),
                BinaryOp::SHR => Ok(lhs.wrapping_shr(rhs as u32)),
                BinaryOp::EQ => Ok((lhs == rhs) as i64),
                BinaryOp::NE => Ok((lhs != rhs) as i64),
                BinaryOp::LT => Ok((lhs < rhs) as i64),
                BinaryOp::LE => Ok((lhs <= rhs) as i64),
                BinaryOp::LOGAND => Ok(((lhs != 0) && (rhs != 0)) as i64),
                BinaryOp::LOGOR => Ok(((lhs != 0) || (rhs != 0)) as i64),
            }
        }
        ExprKind::Unary { op, expr: operand } => {
            let operand = eval(operand, ctx)?;
            match op {
                UnaryOp::NOT => Ok((operand == 0) as i64),
                UnaryOp::BITNOT => Ok(!operand),
                UnaryOp::NEG => Ok(-operand),
                _ => err,
            }
        }
        ExprKind::Cast(operand) => {
            let ty = expr.ty.borrow();
            let operand = eval(operand, ctx)?;
            if ty.is_integer() {
                let sz = ty.size.unwrap();
                if sz == 1 {
                    return Ok(((operand & 0xff) as i8) as i64);
                } else if sz == 2 {
                    return Ok(((operand & 0xffff) as i16) as i64);
                } else if sz == 4 {
                    return Ok(((operand & 0xffffffff) as i32) as i64);
                }
            }
            Ok(operand)
        }
        ExprKind::Cond { cond, then, els } => {
            let cond = eval(cond, ctx)?;
            let then = eval(then, ctx)?;
            let els = eval(els, ctx)?;
            if cond != 0 {
                Ok(then)
            } else {
                Ok(els)
            }
        }
        ExprKind::Comma { rhs, .. } => eval(rhs, ctx),
        ExprKind::Num(val) => Ok(*val),
        _ => err,
    }
}

pub fn program(text: String, filename: &str) -> Result<Program> {
    let mut program = Program::new(text, filename.to_owned());
    let head = tokenize::tokenize(&program.ctx.text, &program.ctx)?;
    let mut tok = head.as_ref();
    program.ctx.enter_scope();
    while !tokenize::at_eof(tok) {
        let spec = declspec(&mut tok, &mut program.ctx, true)?;
        // Function
        if is_func_def(&mut tok, &mut program.ctx)? {
            program
                .funcs
                .push(func(&mut tok, &spec.ty, &spec.attr, &mut program.ctx)?);
            continue;
        }
        // Global variable or function declaration
        if spec.attr.is_typedef {
            parse_typedef(&mut tok, &spec.ty, &mut program.ctx)?;
            continue;
        }
        global_variable(&mut tok, &spec.ty, &mut program.ctx)?;
    }
    Ok(program)
}

fn global_variable(tok: &mut &Token, base_ty: &Rc<RefCell<Type>>, ctx: &mut Context) -> Result<()> {
    let mut first = true;
    while !tokenize::consume_punct(tok, ";") {
        if !first {
            tokenize::expect_punct(tok, ",", ctx)?;
        }
        first = false;
        let decl = declarator(tok, base_ty, ctx)?;
        ctx.new_gvar(&decl);
    }
    Ok(())
}

pub fn func(
    tok: &mut &Token,
    base_ty: &Rc<RefCell<Type>>,
    attr: &VarAttr,
    ctx: &mut Context,
) -> Result<Box<Func>> {
    let loc = tok.loc;
    let decl = declarator(tok, base_ty, ctx)?;
    let ty = decl.ty.borrow();
    if !ty.is_func() {
        return Err(error_message("expected a function", ctx, loc));
    }
    ctx.new_gvar(&decl);
    ctx.return_ty = Rc::clone(&ty.get_return_ty());
    ctx.stack_size = 0;
    ctx.labels.clear();
    ctx.enter_scope();
    let param_decls = ty.get_params();
    let mut params = Vec::new();
    for param_decl in param_decls {
        params.push(ctx.new_lvar(&param_decl));
    }
    let body = compound_stmt(tok, ctx)?;
    ctx.leave_scope();
    ctx.stack_size = align_to(ctx.stack_size, 16);
    Ok(Box::new(Func {
        name: decl.name,
        return_ty: Rc::clone(&ctx.return_ty),
        params,
        body,
        stack_size: ctx.stack_size,
        is_static: attr.is_static,
    }))
}

// Lookahead tokens and returns true if a given token is a start
// of a function definition
fn is_func_def(tok: &mut &Token, ctx: &mut Context) -> Result<bool> {
    if tokenize::equal_punct(tok, ";") {
        return Ok(false);
    }
    let mut cur = *tok;
    let dummy = Type::new_int().wrap();
    ctx.enter_scope();
    let decl = declarator(&mut cur, &dummy, ctx)?;
    let decl_ty = decl.ty.borrow();
    ctx.leave_scope();
    Ok(decl_ty.is_func() && !tokenize::equal_punct(cur, ";"))
}

// declspec = ("void" | "char" | "short" | "int" | "long" |
//             | "typedef" | "static"
//             | struct-decl | union-decl | typedef-name)
//             | enum-specifier)+
// The order of typenames in a type-specifier doesn't matter. For
// example, `int long static` means the same as `static long int`.
// That can also be written as `static long` because you can omit
// `int` if `long` or `short` are specified. However, something like
// `char int` is not valid type specifier. We have to accept only a
// limited combinations of the typenames.
//
// In this function, we count the number of occurences of each typename
// while keeping the "current" type object that the typenames up
// until that point represent. When we reach a non-typename token,
// we returns the current type object.
fn declspec(tok: &mut &Token, ctx: &mut Context, accept_attr: bool) -> Result<DeclSpec> {
    // We use a single integer as counters for all typenames.
    // For example, bits 0 and 1 represents how many times we saw the
    // keyword "void" so far. With this, we can use a match statement
    // as you can see below.
    const VOID: usize = 1 << 0;
    const BOOL: usize = 1 << 2;
    const CHAR: usize = 1 << 4;
    const SHORT: usize = 1 << 6;
    const INT: usize = 1 << 8;
    const LONG: usize = 1 << 10;
    const OTHER: usize = 1 << 12;
    const SHORT_INT: usize = SHORT + INT;
    const LONG_INT: usize = LONG + INT;
    const LONG_LONG: usize = LONG + LONG;
    const LONG_LONG_INT: usize = LONG + LONG + INT;

    let mut ty = Type::new_int().wrap();
    let mut counter = 0;
    let mut attr = VarAttr {
        is_typedef: false,
        is_static: false,
    };
    while is_typename(tok, ctx) {
        let loc = tok.loc;
        // Handle storage class specifiers.
        if tokenize::equal_punct(tok, "typedef") || tokenize::equal_punct(tok, "static") {
            if !accept_attr {
                return Err(error_message(
                    "storage class specifier is not allowed in this context",
                    ctx,
                    loc,
                ));
            }
            if tokenize::equal_punct(tok, "typedef") {
                tokenize::consume_punct(tok, "typedef");
                attr.is_typedef = true;
            } else {
                tokenize::consume_punct(tok, "static");
                attr.is_static = true;
            }
            if attr.is_typedef && attr.is_static {
                return Err(error_message(
                    "typedef and static may not be used together",
                    ctx,
                    loc,
                ));
            }
            continue;
        }
        // Handle user-defined types.
        if tokenize::equal_punct(tok, "struct")
            || tokenize::equal_punct(tok, "union")
            || tokenize::equal_punct(tok, "enum")
            || tokenize::equal_ident(tok)
        {
            if counter > 0 {
                break;
            }
            if tokenize::consume_punct(tok, "struct") {
                ty = struct_union_decl(tok, ctx, true)?;
            } else if tokenize::consume_punct(tok, "union") {
                ty = struct_union_decl(tok, ctx, false)?;
            } else if tokenize::consume_punct(tok, "enum") {
                ty = enum_specifier(tok, ctx)?;
            } else {
                let ident = tokenize::expect_ident(tok, ctx)?;
                ty = ctx.find_var(ident).unwrap().ty;
            }
            counter += OTHER;
            continue;
        }
        // Handle built-in types.
        if tokenize::consume_punct(tok, "void") {
            counter += VOID;
        }
        if tokenize::consume_punct(tok, "_Bool") {
            counter += BOOL;
        }
        if tokenize::consume_punct(tok, "char") {
            counter += CHAR;
        }
        if tokenize::consume_punct(tok, "short") {
            counter += SHORT;
        }
        if tokenize::consume_punct(tok, "int") {
            counter += INT;
        }
        if tokenize::consume_punct(tok, "long") {
            counter += LONG;
        }
        match counter {
            VOID => {
                ty = Type::new_void().wrap();
            }
            BOOL => {
                ty = Type::new_bool().wrap();
            }
            CHAR => {
                ty = Type::new_char().wrap();
            }
            SHORT | SHORT_INT => {
                ty = Type::new_short().wrap();
            }
            INT => {
                ty = Type::new_int().wrap();
            }
            LONG | LONG_INT | LONG_LONG | LONG_LONG_INT => {
                ty = Type::new_long().wrap();
            }
            _ => {
                return Err(error_message("invalid type", ctx, tok.loc));
            }
        }
    }
    Ok(DeclSpec { ty, attr })
}

// func-params = (param ("," param)*)? ")"
// param       = declspec declarator
fn func_params(tok: &mut &Token, ctx: &mut Context) -> Result<Vec<Decl>> {
    let mut params = Vec::new();
    while !tokenize::consume_punct(tok, ")") {
        if params.len() > 0 {
            tokenize::expect_punct(tok, ",", ctx)?;
        }
        let spec = declspec(tok, ctx, false)?;
        let mut param = declarator(tok, &spec.ty, ctx)?;

        // "array of T" is converted to "pointer to T" only in the parameter
        // context. For example, *argv[] is converted to **argv by this.
        if param.ty.borrow().is_array() {
            let Decl { name, ty } = param;
            let ty = ty.borrow();
            let base_ty = ty.get_base_ty();
            param = Decl {
                name,
                ty: Type::new_ptr(&base_ty).wrap(),
            };
        }
        params.push(param);
    }
    Ok(params)
}

// array-dimensions = const-expr? "]" type-suffix
fn array_dimensions(
    tok: &mut &Token,
    ty: &Rc<RefCell<Type>>,
    ctx: &mut Context,
) -> Result<Rc<RefCell<Type>>> {
    let loc = tok.loc;
    if tokenize::consume_punct(tok, "]") {
        let base_ty = type_suffix(tok, ty, ctx)?;
        let array_ty = Type::new_array(&base_ty, None, ctx, loc)?;
        return Ok(array_ty.wrap());
    }
    let len = const_expr(tok, ctx)?;
    tokenize::expect_punct(tok, "]", ctx)?;
    let base_ty = type_suffix(tok, ty, ctx)?;
    let array_ty = Type::new_array(&base_ty, Some(len as usize), ctx, loc)?;
    Ok(array_ty.wrap())
}

// type-suffix = "(" func-params
//             = "[" array-dimensions
//             = ??
fn type_suffix(
    tok: &mut &Token,
    ty: &Rc<RefCell<Type>>,
    ctx: &mut Context,
) -> Result<Rc<RefCell<Type>>> {
    if tokenize::consume_punct(tok, "(") {
        let params = func_params(tok, ctx)?;
        Ok(Type::new_func(params, ty).wrap())
    } else if tokenize::consume_punct(tok, "[") {
        return array_dimensions(tok, ty, ctx);
    } else {
        Ok(Rc::clone(ty))
    }
}

// declarator = "*"* ("(" declarator ")" | ident) type-suffix
fn declarator(tok: &mut &Token, base_ty: &Rc<RefCell<Type>>, ctx: &mut Context) -> Result<Decl> {
    let mut ty = Rc::clone(base_ty);
    while tokenize::consume_punct(tok, "*") {
        ty = Type::new_ptr(&ty).wrap();
    }
    if tokenize::consume_punct(tok, "(") {
        let dummy = Type::new_int().wrap();
        let mut cur = *tok;
        declarator(tok, &dummy, ctx)?;
        tokenize::expect_punct(tok, ")", ctx)?;
        ty = type_suffix(tok, &ty, ctx)?;
        return declarator(&mut cur, &ty, ctx);
    }
    let ident = tokenize::expect_ident(tok, ctx)?;
    ty = type_suffix(tok, &ty, ctx)?;
    Ok(Decl {
        name: ident.to_owned(),
        ty,
    })
}

// abstract-declarator = "*"* ("(" abstract-declarator ")")? type-suffix
fn abstract_declarator(
    tok: &mut &Token,
    base_ty: &Rc<RefCell<Type>>,
    ctx: &mut Context,
) -> Result<Rc<RefCell<Type>>> {
    let mut ty = Rc::clone(base_ty);
    while tokenize::consume_punct(tok, "*") {
        ty = Type::new_ptr(&ty).wrap();
    }
    if tokenize::consume_punct(tok, "(") {
        let dummy = Type::new_int().wrap();
        let mut cur = *tok;
        abstract_declarator(tok, &dummy, ctx)?;
        tokenize::expect_punct(tok, ")", ctx)?;
        ty = type_suffix(tok, &ty, ctx)?;
        return abstract_declarator(&mut cur, &ty, ctx);
    }
    type_suffix(tok, &ty, ctx)
}

// type-name = declspec abstract-declarator
fn typename(tok: &mut &Token, ctx: &mut Context) -> Result<Rc<RefCell<Type>>> {
    let spec = declspec(tok, ctx, false)?;
    abstract_declarator(tok, &spec.ty, ctx)
}

// declaration = declspec (declarator ("=" initializer)? ("," declarator ("=" initializer?)*)? ";"
fn declaration(
    tok: &mut &Token,
    ctx: &mut Context,
    base_ty: &Rc<RefCell<Type>>,
) -> Result<Vec<Box<Stmt>>> {
    let mut stmt_vec = Vec::new();
    let mut count = 0;
    while !tokenize::consume_punct(tok, ";") {
        if count > 0 {
            tokenize::expect_punct(tok, ",", ctx)?;
        }
        let loc = tok.loc;
        let decl = declarator(tok, base_ty, ctx)?;
        if decl.ty.borrow().is_void() {
            return Err(error_message("variable declared void", ctx, loc));
        }
        let obj = ctx.new_lvar(&decl);
        if tokenize::consume_punct(tok, "=") {
            let init = initializer(tok, ctx, &obj.ty)?;
            let init = init.to_lvar_init(&obj.ty, obj.get_offset(), loc);

            // If a partial initializer list is given, the standard requires
            // that unspecified elements are set to 0. Here, we simply
            // zero-initialize the entire memory region of a variable before
            // initializing it with user-supplied values.
            let init = Expr::new_comma(Expr::new_memzero(obj, loc), init, loc);
            stmt_vec.push(Box::new(Stmt {
                kind: StmtKind::ExprStmt(init),
                loc,
            }))
        }
        count += 1;
    }
    Ok(stmt_vec)
}

fn skip_excess_element(tok: &mut &Token, ctx: &mut Context) -> Result<()> {
    if tokenize::consume_punct(tok, "{") {
        skip_excess_element(tok, ctx)?;
        tokenize::expect_punct(tok, "}", ctx)?;
    } else {
        assign(tok, ctx)?;
    }
    Ok(())
}

// initializer = "{" initializer ("," initializer)* "}"
//             | assign
fn initializer(
    tok: &mut &Token,
    ctx: &mut Context,
    ty: &Rc<RefCell<Type>>,
) -> Result<Box<Initializer>> {
    let ty = ty.borrow();
    if ty.is_array() {
        tokenize::expect_punct(tok, "{", ctx)?;
        let mut init = Vec::new();
        let mut i = 0;
        let array_len = ty.get_array_len();
        while !tokenize::consume_punct(tok, "}") {
            if i > 0 {
                tokenize::expect_punct(tok, ",", ctx)?;
            }
            if i < array_len {
                init.push(initializer(tok, ctx, ty.get_base_ty())?);
            } else {
                skip_excess_element(tok, ctx)?;
            }
            i += 1;
        }
        return Ok(Box::new(Initializer::Compound(init)));
    }
    Ok(Box::new(Initializer::Scalar(assign(tok, ctx)?)))
}

// Returns true if a given token represents a type.
fn is_typename(tok: &Token, ctx: &Context) -> bool {
    if tokenize::equal_ident(tok) {
        let obj = ctx.find_var(&tok.text);
        return obj.is_some() && obj.unwrap().is_typedef();
    }
    tokenize::equal_punct(tok, "void")
        || tokenize::equal_punct(tok, "_Bool")
        || tokenize::equal_punct(tok, "char")
        || tokenize::equal_punct(tok, "short")
        || tokenize::equal_punct(tok, "int")
        || tokenize::equal_punct(tok, "long")
        || tokenize::equal_punct(tok, "struct")
        || tokenize::equal_punct(tok, "union")
        || tokenize::equal_punct(tok, "enum")
        || tokenize::equal_punct(tok, "typedef")
        || tokenize::equal_punct(tok, "static")
}

// struct-members = (declspec declarator ("," declarator)* ";")* "}"
fn struct_members(tok: &mut &Token, ctx: &mut Context) -> Result<Vec<Decl>> {
    let mut member_decls = Vec::new();
    while !tokenize::consume_punct(tok, "}") {
        let spec = declspec(tok, ctx, false)?;
        let mut first = true;
        while !tokenize::consume_punct(tok, ";") {
            if !first {
                tokenize::expect_punct(tok, ",", ctx)?;
            }
            first = false;
            let member_decl = declarator(tok, &spec.ty, ctx)?;
            member_decls.push(member_decl);
        }
    }
    Ok(member_decls)
}

// struct-union-decl = ident? ("{" struct-members)?
fn struct_union_decl(
    tok: &mut &Token,
    ctx: &mut Context,
    is_struct: bool,
) -> Result<Rc<RefCell<Type>>> {
    // Read a tag.
    let tag = tokenize::consume_ident(tok);
    if tag.is_some() && !tokenize::equal_punct(tok, "{") {
        let tag = tag.unwrap();
        if let Some(ty) = ctx.find_tag(tag) {
            return Ok(ty);
        } else {
            let ty;
            if is_struct {
                ty = Type::new_struct(Vec::new());
            } else {
                ty = Type::new_union(Vec::new());
            }
            let ty = ty.wrap();
            ctx.new_tag(tag, &ty);
            return Ok(ty);
        }
    }
    tokenize::consume_punct(tok, "{");
    let member_decls = struct_members(tok, ctx)?;
    let struct_ty;
    if is_struct {
        struct_ty = Type::new_struct(member_decls);
    } else {
        struct_ty = Type::new_union(member_decls);
    }
    if let Some(tag) = tag {
        // If this is a redefinition, overwrite a previous type.
        // Otherwise, register the struct type.
        if let Some(ty) = ctx.find_tag_in_current_scope(tag) {
            *ty.borrow_mut() = struct_ty;
            return Ok(ty);
        } else {
            let ty = struct_ty.wrap();
            ctx.new_tag(tag, &ty);
            return Ok(ty);
        }
    } else {
        Ok(struct_ty.wrap())
    }
}

fn enum_specifier(tok: &mut &Token, ctx: &mut Context) -> Result<Rc<RefCell<Type>>> {
    let loc = tok.loc;
    let enum_ty = Type::new_enum().wrap();
    // Read a tag.
    let tag = tokenize::consume_ident(tok);
    if tag.is_some() && !tokenize::equal_punct(tok, "{") {
        let ty = ctx.find_tag(tag.unwrap());
        if ty.is_none() {
            return Err(error_message("unknown enum type", ctx, loc));
        }
        let ty = ty.unwrap();
        if !ty.borrow().is_enum() {
            return Err(error_message("not an enum tag", ctx, loc));
        }
        return Ok(ty);
    }
    tokenize::consume_punct(tok, "{");
    // Read an enum-list
    let mut first = true;
    let mut val = 0;
    while !tokenize::consume_punct(tok, "}") {
        if !first {
            tokenize::expect_punct(tok, ",", ctx)?;
        }
        first = false;
        let name = tokenize::expect_ident(tok, ctx)?;
        if tokenize::consume_punct(tok, "=") {
            val = const_expr(tok, ctx)?;
        }
        ctx.new_enum_const(name, val);
        val += 1;
    }
    if let Some(tag) = tag {
        ctx.new_tag(tag, &enum_ty);
    }
    Ok(enum_ty)
}

fn parse_typedef(tok: &mut &Token, base_ty: &Rc<RefCell<Type>>, ctx: &mut Context) -> Result<()> {
    let mut first = true;

    while !tokenize::consume_punct(tok, ";") {
        if !first {
            tokenize::consume_punct(tok, ",");
        }
        first = false;

        let decl = declarator(tok, base_ty, ctx)?;
        ctx.new_typedef(&decl);
    }
    Ok(())
}

// stmt = "return" expr ";"
//      | "if" "(" expr ")" stmt ("else" stmt)?
//      | "switch" "(" expr ")" stmt
//      | "case" const-expr":" stmt
//      | "default" ":" stmt
//      | "for" "(" expr-stmt? ";" expr? ";" expr? ")" stmt
//      | "while" "(" expr ")" stmt
//      | "goto" ident ";"
//      | "break" ";"
//      | ident ":" stmt
//      | "{" block-item* "}"
//      | expr-stmt
//      | null-stmt
fn stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    if tokenize::equal_punct(tok, ";") {
        Ok(null_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "return") {
        Ok(return_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "{") {
        Ok(compound_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "if") {
        Ok(if_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "switch") {
        Ok(switch_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "case") {
        Ok(case_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "default") {
        Ok(default_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "for") {
        Ok(for_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "while") {
        Ok(while_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "goto") {
        Ok(goto_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "break") {
        Ok(break_stmt(tok, ctx)?)
    } else if tokenize::equal_punct(tok, "continue") {
        Ok(continue_stmt(tok, ctx)?)
    } else if tokenize::equal_ident(tok) && tokenize::equal_punct(tok.next.as_ref().unwrap(), ":") {
        Ok(labeled_stmt(tok, ctx)?)
    } else {
        Ok(expr_stmt(tok, ctx)?)
    }
}

fn null_stmt(tok: &mut &Token, ctx: &Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect_punct(tok, ";", ctx)?;
    let stmt = Stmt {
        kind: StmtKind::NullStmt,
        loc,
    };
    Ok(Box::new(stmt))
}

fn return_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect_punct(tok, "return", ctx)?;
    let mut expr = expr(tok, ctx)?;
    tokenize::expect_punct(tok, ";", ctx)?;
    expr = Expr::new_cast(expr, &ctx.return_ty, loc);
    Ok(Box::new(Stmt {
        kind: StmtKind::ReturnStmt(expr),
        loc,
    }))
}

// compound-stmt = (typedef | declaration | stmt)* "}"
fn compound_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect_punct(tok, "{", ctx)?;
    let mut block = Vec::new();
    ctx.enter_scope();
    while !tokenize::consume_punct(tok, "}") {
        if is_typename(tok, ctx) && !tokenize::equal_punct(tok.next.as_ref().unwrap(), ":") {
            let spec = declspec(tok, ctx, true)?;
            if spec.attr.is_typedef {
                parse_typedef(tok, &spec.ty, ctx)?;
                continue;
            }
            let init = declaration(tok, ctx, &spec.ty)?;
            block.extend(init.into_iter());
        } else {
            block.push(stmt(tok, ctx)?);
        }
    }
    ctx.leave_scope();
    let stmt = Stmt {
        kind: StmtKind::CompoundStmt(block),
        loc,
    };
    Ok(Box::new(stmt))
}

fn expr_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    let stmt = Stmt {
        kind: StmtKind::ExprStmt(expr(tok, ctx)?),
        loc,
    };
    tokenize::expect_punct(tok, ";", ctx)?;
    Ok(Box::new(stmt))
}

fn if_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect_punct(tok, "if", ctx)?;
    tokenize::expect_punct(tok, "(", ctx)?;
    let cond = expr(tok, ctx)?;
    tokenize::expect_punct(tok, ")", ctx)?;
    let then = stmt(tok, ctx)?;
    let mut els = None;
    if tokenize::consume_punct(tok, "else") {
        els = Some(stmt(tok, ctx)?);
    }
    let stmt = Stmt {
        kind: StmtKind::IfStmt { cond, then, els },
        loc,
    };
    Ok(Box::new(stmt))
}

fn switch_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let prev_case = ctx.case_labels.take();
    ctx.case_labels = Some(Vec::new());
    let prev_default = ctx.default_label.take();
    let break_label = ctx.new_unique_name();
    let prev_break = ctx.break_label.take();
    ctx.break_label = Some(break_label.clone());
    let loc = tok.loc;
    tokenize::expect_punct(tok, "switch", ctx)?;
    tokenize::expect_punct(tok, "(", ctx)?;
    let cond = expr(tok, ctx)?;
    tokenize::expect_punct(tok, ")", ctx)?;
    let body = stmt(tok, ctx)?;
    let case_labels = ctx.case_labels.take().unwrap();
    let default_label = ctx.default_label.take();
    let stmt = Stmt {
        kind: StmtKind::SwitchStmt {
            cond,
            body,
            case_labels,
            default_label,
            break_label,
        },
        loc,
    };
    ctx.case_labels = prev_case;
    ctx.default_label = prev_default;
    ctx.break_label = prev_break;
    Ok(Box::new(stmt))
}

fn case_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let case_label = ctx.new_unique_name();
    let loc = tok.loc;
    tokenize::expect_punct(tok, "case", ctx)?;
    let num = const_expr(tok, ctx)?;
    tokenize::expect_punct(tok, ":", ctx)?;
    if ctx.case_labels.is_none() {
        return Err(error_message("stray case", ctx, loc));
    }
    let case_labels = ctx.case_labels.as_mut().unwrap();
    case_labels.push((num, case_label.clone()));
    Ok(Box::new(Stmt {
        kind: StmtKind::LabeledStmt(case_label, stmt(tok, ctx)?),
        loc,
    }))
}

fn default_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect_punct(tok, "default", ctx)?;
    tokenize::expect_punct(tok, ":", ctx)?;
    let default_label = ctx.new_unique_name();
    ctx.default_label = Some(default_label.clone());
    Ok(Box::new(Stmt {
        kind: StmtKind::LabeledStmt(default_label, stmt(tok, ctx)?),
        loc,
    }))
}

fn for_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let break_label = ctx.new_unique_name();
    let prev_break = ctx.break_label.take();
    ctx.break_label = Some(break_label.clone());
    let continue_label = ctx.new_unique_name();
    let prev_continue = ctx.continue_label.take();
    ctx.continue_label = Some(continue_label.clone());
    let loc = tok.loc;
    tokenize::expect_punct(tok, "for", ctx)?;
    tokenize::expect_punct(tok, "(", ctx)?;
    ctx.enter_scope();
    let init;
    if is_typename(tok, ctx) {
        let spec = declspec(tok, ctx, false)?;
        init = declaration(tok, ctx, &spec.ty)?;
    } else {
        init = vec![stmt(tok, ctx)?];
    }
    let mut cond = None;
    if !tokenize::equal_punct(tok, ";") {
        cond = Some(expr(tok, ctx)?);
    }
    tokenize::expect_punct(tok, ";", ctx)?;
    let mut inc = None;
    if !tokenize::equal_punct(tok, ")") {
        inc = Some(expr(tok, ctx)?);
    }
    tokenize::expect_punct(tok, ")", ctx)?;
    let body = stmt(tok, ctx)?;
    ctx.leave_scope();
    let stmt = Stmt {
        kind: StmtKind::ForStmt {
            init,
            cond,
            inc,
            body,
            break_label,
            continue_label,
        },
        loc,
    };
    ctx.break_label = prev_break;
    ctx.continue_label = prev_continue;
    Ok(Box::new(stmt))
}

fn while_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let break_label = ctx.new_unique_name();
    let prev_break = ctx.break_label.take();
    ctx.break_label = Some(break_label.clone());
    let continue_label = ctx.new_unique_name();
    let prev_continue = ctx.continue_label.take();
    ctx.continue_label = Some(continue_label.clone());
    let loc = tok.loc;
    tokenize::expect_punct(tok, "while", ctx)?;
    tokenize::expect_punct(tok, "(", ctx)?;
    let cond = expr(tok, ctx)?;
    tokenize::expect_punct(tok, ")", ctx)?;
    let body = stmt(tok, ctx)?;
    let stmt = Stmt {
        kind: StmtKind::WhileStmt {
            cond,
            body,
            break_label,
            continue_label,
        },
        loc,
    };
    ctx.break_label = prev_break;
    ctx.continue_label = prev_continue;
    Ok(Box::new(stmt))
}

fn goto_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect_punct(tok, "goto", ctx)?;
    let ident = tokenize::expect_ident(tok, ctx)?;
    let unique_name;
    if let Some(name) = ctx.labels.get(ident) {
        unique_name = name.clone();
    } else {
        unique_name = ctx.new_unique_name();
        ctx.labels.insert(ident.to_owned(), unique_name.clone());
    }
    tokenize::expect_punct(tok, ";", ctx)?;
    Ok(Box::new(Stmt {
        kind: StmtKind::GotoStmt(unique_name),
        loc,
    }))
}

fn break_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect_punct(tok, "break", ctx)?;
    tokenize::expect_punct(tok, ";", ctx)?;
    if ctx.break_label.is_none() {
        return Err(error_message("stray break", ctx, loc));
    }
    Ok(Box::new(Stmt {
        kind: StmtKind::GotoStmt(ctx.break_label.as_ref().unwrap().clone()),
        loc,
    }))
}

fn continue_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect_punct(tok, "continue", ctx)?;
    tokenize::expect_punct(tok, ";", ctx)?;
    if ctx.continue_label.is_none() {
        return Err(error_message("stray continue", ctx, loc));
    }
    Ok(Box::new(Stmt {
        kind: StmtKind::GotoStmt(ctx.continue_label.as_ref().unwrap().clone()),
        loc,
    }))
}

fn labeled_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    let ident = tokenize::expect_ident(tok, ctx)?;
    tokenize::expect_punct(tok, ":", ctx)?;
    let unique_name;
    if let Some(name) = ctx.labels.get(ident) {
        unique_name = name.clone();
    } else {
        unique_name = ctx.new_unique_name();
        ctx.labels.insert(ident.to_owned(), unique_name.clone());
    }
    Ok(Box::new(Stmt {
        kind: StmtKind::LabeledStmt(unique_name, stmt(tok, ctx)?),
        loc,
    }))
}

// expr = assign ("," expr)?
fn expr(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let lhs = assign(tok, ctx)?;
    if tokenize::equal_punct(tok, ",") {
        let loc = tok.loc;
        tokenize::consume_punct(tok, ",");
        let rhs = expr(tok, ctx)?;
        return Ok(Expr::new_comma(lhs, rhs, loc));
    }
    Ok(lhs)
}

fn const_expr(tok: &mut &Token, ctx: &mut Context) -> Result<i64> {
    let expr = conditional(tok, ctx)?;
    eval(&expr, ctx)
}

// assign = conditional (assign-op assign)?
// assign-op = "=" | "+=" | "-=" | "*=" | "/=" | "&=" | "|=" | "^="
//           | "<<=" | ">>="
fn assign(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let lhs = conditional(tok, ctx)?;
    let loc = tok.loc;
    if tokenize::consume_punct(tok, "=") {
        Ok(Expr::new_assign(lhs, assign(tok, ctx)?, loc))
    } else if tokenize::consume_punct(tok, "+=") {
        Expr::new_op_assign(BinaryOp::ADD, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, "-=") {
        Expr::new_op_assign(BinaryOp::SUB, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, "*=") {
        Expr::new_op_assign(BinaryOp::MUL, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, "/=") {
        Expr::new_op_assign(BinaryOp::DIV, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, "%=") {
        Expr::new_op_assign(BinaryOp::MOD, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, "&=") {
        Expr::new_op_assign(BinaryOp::BITAND, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, "|=") {
        Expr::new_op_assign(BinaryOp::BITOR, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, "^=") {
        Expr::new_op_assign(BinaryOp::BITXOR, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, "<<=") {
        Expr::new_op_assign(BinaryOp::SHL, lhs, assign(tok, ctx)?, ctx, loc)
    } else if tokenize::consume_punct(tok, ">>=") {
        Expr::new_op_assign(BinaryOp::SHR, lhs, assign(tok, ctx)?, ctx, loc)
    } else {
        Ok(lhs)
    }
}

// conditional = logor ("?" expr ":" conditional)?
fn conditional(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let loc = tok.loc;
    let cond = logor(tok, ctx)?;
    if !tokenize::equal_punct(tok, "?") {
        return Ok(cond);
    }
    tokenize::expect_punct(tok, "?", ctx)?;
    let mut then = expr(tok, ctx)?;
    tokenize::expect_punct(tok, ":", ctx)?;
    let mut els = conditional(tok, ctx)?;
    let result_ty;
    if then.ty.borrow().is_void() || els.ty.borrow().is_void() {
        result_ty = Type::new_void().wrap();
    } else {
        (then, els) = usual_arith_conv(then, els);
        result_ty = Rc::clone(&then.ty);
    }
    Ok(Box::new(Expr {
        kind: ExprKind::Cond { cond, then, els },
        ty: result_ty,
        loc,
    }))
}

// logor = logand ("||" logand)*
fn logor(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = logand(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "||") {
            expr = Expr::new_binary(BinaryOp::LOGOR, expr, logand(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// logand = bitor ("&&" bitor)*
fn logand(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = bitor(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "&&") {
            expr = Expr::new_binary(BinaryOp::LOGAND, expr, bitor(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// bitor= bitxor ("^" bitxor)*
fn bitor(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = bitxor(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "|") {
            expr = Expr::new_binary(BinaryOp::BITOR, expr, bitxor(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// bitxor= bitand ("^" bitand)*
fn bitxor(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = bitand(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "^") {
            expr = Expr::new_binary(BinaryOp::BITXOR, expr, bitand(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// bitand = equality ("&" equality)*
fn bitand(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = equality(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "&") {
            expr = Expr::new_binary(BinaryOp::BITAND, expr, equality(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// equality = relational ("==" relational | "!=" relational)*
fn equality(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = relational(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "==") {
            expr = Expr::new_binary(BinaryOp::EQ, expr, relational(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume_punct(tok, "!=") {
            expr = Expr::new_binary(BinaryOp::NE, expr, relational(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// relational = shift ("<" shift | "<=" shift | ">" shift | ">=" shift)*
fn relational(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = shift(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "<") {
            expr = Expr::new_binary(BinaryOp::LT, expr, shift(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume_punct(tok, "<=") {
            expr = Expr::new_binary(BinaryOp::LE, expr, shift(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume_punct(tok, ">") {
            expr = Expr::new_binary(BinaryOp::LT, shift(tok, ctx)?, expr, ctx, loc)?;
            continue;
        }
        if tokenize::consume_punct(tok, ">=") {
            expr = Expr::new_binary(BinaryOp::LE, shift(tok, ctx)?, expr, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// shift = add ("<<" add | ">>" add)*
fn shift(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = add(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "<<") {
            let rhs = add(tok, ctx)?;
            expr = Expr::new_binary(BinaryOp::SHL, expr, rhs, ctx, loc)?;
            continue;
        }
        if tokenize::consume_punct(tok, ">>") {
            let rhs = add(tok, ctx)?;
            expr = Expr::new_binary(BinaryOp::SHR, expr, rhs, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// add = mul ("+" mul | "-" mul)*
fn add(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = mul(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "+") {
            let rhs = mul(tok, ctx)?;
            expr = Expr::new_binary(BinaryOp::ADD, expr, rhs, ctx, loc)?;
            continue;
        }
        if tokenize::consume_punct(tok, "-") {
            let rhs = mul(tok, ctx)?;
            expr = Expr::new_binary(BinaryOp::SUB, expr, rhs, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// mul = cast ("*" cast | "/" cast | "%" cast)*
fn mul(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = cast(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "*") {
            expr = Expr::new_binary(BinaryOp::MUL, expr, cast(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume_punct(tok, "/") {
            expr = Expr::new_binary(BinaryOp::DIV, expr, cast(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume_punct(tok, "%") {
            expr = Expr::new_binary(BinaryOp::MOD, expr, cast(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// cast = "(" type-name ")" cast | unary
fn cast(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let loc = tok.loc;
    let mut cur = *tok;
    if tokenize::consume_punct(&mut cur, "(") && is_typename(&mut cur, ctx) {
        *tok = cur;
        let ty = typename(tok, ctx)?;
        tokenize::expect_punct(tok, ")", ctx)?;
        Ok(Expr::new_cast(cast(tok, ctx)?, &ty, loc))
    } else {
        unary(tok, ctx)
    }
}

// unary = ("+" | "-" | "*" | "&" | "!" | "~") cast
//       | ("++" | "--") unary
//       | postfix
fn unary(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let loc = tok.loc;
    if tokenize::consume_punct(tok, "+") {
        cast(tok, ctx)
    } else if tokenize::consume_punct(tok, "-") {
        Ok(Expr::new_unary(UnaryOp::NEG, cast(tok, ctx)?, ctx, loc)?)
    } else if tokenize::consume_punct(tok, "*") {
        Ok(Expr::new_unary(UnaryOp::DEREF, cast(tok, ctx)?, ctx, loc)?)
    } else if tokenize::consume_punct(tok, "&") {
        Ok(Expr::new_unary(UnaryOp::ADDR, cast(tok, ctx)?, ctx, loc)?)
    } else if tokenize::consume_punct(tok, "!") {
        Ok(Expr::new_unary(UnaryOp::NOT, cast(tok, ctx)?, ctx, loc)?)
    } else if tokenize::consume_punct(tok, "~") {
        Ok(Expr::new_unary(UnaryOp::BITNOT, cast(tok, ctx)?, ctx, loc)?)
    } else if tokenize::consume_punct(tok, "++") {
        Expr::new_op_assign(
            BinaryOp::ADD,
            unary(tok, ctx)?,
            Expr::new_num(1, loc),
            ctx,
            loc,
        )
    } else if tokenize::consume_punct(tok, "--") {
        Expr::new_op_assign(
            BinaryOp::SUB,
            unary(tok, ctx)?,
            Expr::new_num(1, loc),
            ctx,
            loc,
        )
    } else {
        postfix(tok, ctx)
    }
}

// postfix = primary ("[" expr "]" | "." ident | "->" ident | "++" | "--")*
fn postfix(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut ret = primary(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume_punct(tok, "[") {
            let index = expr(tok, ctx)?;
            tokenize::expect_punct(tok, "]", ctx)?;
            ret = Expr::new_unary(
                UnaryOp::DEREF,
                Expr::new_binary(BinaryOp::ADD, ret, index, ctx, loc)?,
                ctx,
                loc,
            )?;
        } else if tokenize::consume_punct(tok, ".") {
            let name = tokenize::expect_ident(tok, ctx)?;
            ret = Expr::new_member(ret, name, ctx, loc)?;
        } else if tokenize::consume_punct(tok, "->") {
            ret = Expr::new_unary(UnaryOp::DEREF, ret, ctx, loc)?;
            let name = tokenize::expect_ident(tok, ctx)?;
            ret = Expr::new_member(ret, name, ctx, loc)?;
        } else if tokenize::consume_punct(tok, "++") {
            ret = Expr::new_inc_dec(ret, 1, ctx, loc)?;
        } else if tokenize::consume_punct(tok, "--") {
            ret = Expr::new_inc_dec(ret, -1, ctx, loc)?;
        } else {
            break;
        }
    }
    Ok(ret)
}

fn stmt_expr(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let loc = tok.loc;
    let stmt = compound_stmt(tok, ctx)?;
    let body = stmt.get_body();
    if body.is_empty() {
        return Err(error_message(
            "statement expression returning void is not supported",
            ctx,
            loc,
        ));
    }
    if let StmtKind::ExprStmt(last_expr) = &body.last().unwrap().kind {
        let ty = Rc::clone(&last_expr.ty);
        let expr = Expr {
            kind: ExprKind::StmtExpr(body),
            ty,
            loc,
        };
        return Ok(Box::new(expr));
    } else {
        return Err(error_message(
            "statement expression returning void is not supported",
            ctx,
            loc,
        ));
    }
}

// primary = "(" "{" stmt+ "}" ")"
//         | "(" expr ")"
//         | "sizeof" "(" type-name ")"
//         | "sizeof" unary
//         | ident func-args?
//         | str
//         | num
//
// func-args = "(" (expr ("," expr)*)? ")"
fn primary(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let loc = tok.loc;

    if tokenize::consume_punct(tok, "(") {
        let inner;
        if tokenize::equal_punct(tok, "{") {
            inner = stmt_expr(tok, ctx)?;
        } else {
            inner = expr(tok, ctx)?
        }
        tokenize::expect_punct(tok, ")", ctx)?;
        return Ok(inner);
    }

    if tokenize::consume_punct(tok, "sizeof") {
        let mut cur = *tok;
        if tokenize::consume_punct(&mut cur, "(") && is_typename(cur, ctx) {
            *tok = cur;
            let ty = typename(tok, ctx)?;
            let size = ty.borrow().size;
            if size.is_none() {
                return Err(error_message("invalid operand", ctx, loc));
            }
            tokenize::expect_punct(tok, ")", ctx)?;
            return Ok(Expr::new_num(size.unwrap() as i64, loc));
        }
        let expr = unary(tok, ctx)?;
        let size = expr.ty.borrow().size;
        if size.is_none() {
            return Err(error_message("invalid operand", ctx, loc));
        }
        return Ok(Expr::new_num(size.unwrap() as i64, loc));
    }

    if let Some(val) = tokenize::consume_number(tok) {
        return Ok(Expr::new_num(val, loc));
    }

    if let Some(ident) = tokenize::consume_ident(tok) {
        let obj = ctx.find_var(&ident);
        if obj.is_none() {
            return Err(error_message("unknown identifier", ctx, loc));
        }
        let obj = obj.unwrap();
        // Function call
        if tokenize::consume_punct(tok, "(") {
            if !obj.is_global() || !obj.ty.borrow().is_func() {
                return Err(error_message("not a function", ctx, loc));
            }
            let ty = obj.ty.borrow();
            let return_ty = ty.get_return_ty();
            let mut params = ty.get_params().iter();
            let mut args = Vec::new();
            while !tokenize::consume_punct(tok, ")") {
                let loc = tok.loc;
                if args.len() > 0 {
                    tokenize::expect_punct(tok, ",", ctx)?;
                }
                let param = params.next().unwrap();
                let mut arg = assign(tok, ctx)?;
                arg = Expr::new_cast(arg, &param.ty, loc);
                args.push(arg);
            }
            return Ok(Expr::new_funcall(ident, args, return_ty, loc));
        }
        // Enum
        if let ObjKind::Enum(val) = obj.kind {
            return Ok(Expr::new_num(val, loc));
        }
        // Variable
        if obj.is_typedef() {
            return Err(error_message("not a variable", ctx, loc));
        }
        return Ok(Expr::new_var(obj, loc));
    }

    if let Some(bytes) = tokenize::consume_str(tok) {
        let obj = ctx.new_str(bytes.clone(), loc);
        return Ok(Expr::new_var(obj, loc));
    }

    Err(error_message("expected an expression", ctx, loc))
}
