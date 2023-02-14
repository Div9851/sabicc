use anyhow::{bail, Result};
use std::mem;
use std::rc::Rc;

use crate::tokenize::{self, Token, TokenKind};
use crate::{align_to, error_message, Context, Decl, Obj, Type, TypeKind};

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
    pub return_ty: Rc<Type>,
    pub params: Vec<Obj>,
    pub body: Box<Stmt>,
    pub stack_size: usize,
}

pub enum StmtKind {
    DeclStmt(Vec<Box<Stmt>>),
    NullStmt,
    ReturnStmt(Box<Expr>),
    CompoundStmt(Vec<Box<Stmt>>),
    ExprStmt(Box<Expr>),
    IfStmt {
        cond: Box<Expr>,
        then: Box<Stmt>,
        els: Option<Box<Stmt>>,
    },
    ForStmt {
        init: Box<Stmt>,
        cond: Option<Box<Expr>>,
        inc: Option<Box<Expr>>,
        body: Box<Stmt>,
    },
    WhileStmt {
        cond: Box<Expr>,
        body: Box<Stmt>,
    },
}

pub struct Stmt {
    pub kind: StmtKind,
    pub loc: usize,
}

#[derive(Clone, Copy)]
pub enum BinaryOp {
    ADD,   // +
    SUB,   // -
    MUL,   // *
    DIV,   // /
    EQ,    // ==
    NE,    // !=
    LT,    // <
    LE,    // <=
    COMMA, // ,
}

#[derive(Clone, Copy)]
pub enum UnaryOp {
    NEG,   // -
    DEREF, // *
    ADDR,  // &
}

pub enum ExprKind {
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
    Member {
        expr: Box<Expr>,
        offset: usize,
    },
    Var(Obj),
    Num(i32),
    FunCall {
        name: String,
        args: Vec<Box<Expr>>,
    },
}

pub struct Expr {
    pub kind: ExprKind,
    pub ty: Rc<Type>,
    pub loc: usize,
}

impl Expr {
    fn new_assign(lhs: Box<Expr>, rhs: Box<Expr>, loc: usize) -> Box<Expr> {
        let result_ty = Rc::clone(&lhs.ty);
        Box::new(Expr {
            kind: ExprKind::Assign { lhs, rhs },
            ty: result_ty,
            loc,
        })
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
            BinaryOp::MUL | BinaryOp::DIV => {
                if lhs.ty.is_integer() && rhs.ty.is_integer() {
                    let expr = Expr {
                        kind: ExprKind::Binary { op, lhs, rhs },
                        ty: Type::new_int(),
                        loc,
                    };
                    Ok(Box::new(expr))
                } else {
                    panic!("invalid operands");
                }
            }
            BinaryOp::EQ | BinaryOp::NE | BinaryOp::LT | BinaryOp::LE => {
                let expr = Expr {
                    kind: ExprKind::Binary { op, lhs, rhs },
                    ty: Type::new_int(),
                    loc,
                };
                Ok(Box::new(expr))
            }
            BinaryOp::COMMA => {
                let ty = Rc::clone(&rhs.ty);
                let expr = Expr {
                    kind: ExprKind::Binary { op, lhs, rhs },
                    ty,
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
        if lhs.ty.is_integer() && rhs.ty.is_ptr() {
            mem::swap(&mut lhs, &mut rhs);
        }
        let result_ty;
        if lhs.ty.is_integer() && rhs.ty.is_integer() {
            // `int + int`
            result_ty = Type::new_int();
        } else if lhs.ty.is_ptr() && rhs.ty.is_integer() {
            // `ptr + int`
            rhs = Expr::new_binary(
                BinaryOp::MUL,
                rhs,
                Expr::new_num(lhs.ty.get_base_ty().size as i32, loc),
                ctx,
                loc,
            )?;
            result_ty = Rc::clone(&lhs.ty);
        } else {
            // `ptr + ptr`
            bail!(error_message("invalid operands", ctx, loc));
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

    fn new_sub(lhs: Box<Expr>, mut rhs: Box<Expr>, ctx: &Context, loc: usize) -> Result<Box<Expr>> {
        let result_ty;
        let mut div = 1;
        if lhs.ty.is_integer() && rhs.ty.is_integer() {
            // `int - int`
            result_ty = Type::new_int();
        } else if lhs.ty.is_ptr() && rhs.ty.is_integer() {
            // `ptr - int`
            rhs = Expr::new_binary(
                BinaryOp::MUL,
                rhs,
                Expr::new_num(lhs.ty.get_base_ty().size as i32, loc),
                ctx,
                loc,
            )?;
            result_ty = Rc::clone(&lhs.ty);
        } else if lhs.ty.is_integer() && rhs.ty.is_ptr() {
            // `int - ptr`
            bail!(error_message("invalid operands", ctx, loc));
        } else {
            // `ptr - ptr`
            // todo: type check
            div = lhs.ty.get_base_ty().size as i32;
            result_ty = Type::new_int();
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

    fn new_unary(op: UnaryOp, expr: Box<Expr>, ctx: &Context, loc: usize) -> Result<Box<Expr>> {
        let result_ty;
        match op {
            UnaryOp::NEG => {
                if expr.ty.is_integer() {
                    result_ty = Type::new_int();
                } else {
                    bail!(error_message("invalid operand", ctx, loc));
                }
            }
            UnaryOp::DEREF => {
                if expr.ty.is_ptr() {
                    result_ty = Rc::clone(expr.ty.get_base_ty());
                } else {
                    bail!(error_message("invalid operand", ctx, loc));
                }
            }
            UnaryOp::ADDR => {
                result_ty = Type::new_ptr(&expr.ty);
            }
        }
        Ok(Box::new(Expr {
            kind: ExprKind::Unary { op, expr },
            ty: result_ty,
            loc,
        }))
    }

    fn new_member(expr: Box<Expr>, name: &str, ctx: &Context, loc: usize) -> Result<Box<Expr>> {
        let offset;
        let ty;
        if let TypeKind::Struct(members) = &expr.ty.kind {
            if let Some(member) = members.get(name) {
                offset = member.offset;
                ty = Rc::clone(&member.ty);
            } else {
                bail!(error_message("no such member", ctx, loc));
            }
        } else {
            bail!(error_message("not struct", ctx, expr.loc));
        }
        Ok(Box::new(Expr {
            kind: ExprKind::Member { expr, offset },
            ty,
            loc,
        }))
    }

    fn new_var(obj: Obj, loc: usize) -> Box<Expr> {
        let ty = Rc::clone(&obj.ty);
        Box::new(Expr {
            kind: ExprKind::Var(obj),
            ty,
            loc,
        })
    }

    fn new_num(val: i32, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Num(val),
            ty: Type::new_int(),
            loc,
        })
    }

    fn new_funcall(name: &str, args: Vec<Box<Expr>>, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::FunCall {
                name: name.to_owned(),
                args,
            },
            ty: Type::new_int(),
            loc,
        })
    }
}

pub fn program(text: String, filename: &str) -> Result<Program> {
    let mut program = Program::new(text, filename.to_owned());
    let head = tokenize::tokenize(&program.ctx.text, &program.ctx)?;
    let mut tok = head.as_ref();
    program.ctx.enter_scope();
    while !tokenize::at_eof(tok) {
        let base_ty = declspec(&mut tok, &mut program.ctx)?;
        // Function
        if is_func(&mut tok, &mut program.ctx)? {
            program
                .funcs
                .push(func(&mut tok, &base_ty, &mut program.ctx)?);
            continue;
        }
        // Global variable
        global_variable(&mut tok, &base_ty, &mut program.ctx)?;
    }
    Ok(program)
}

fn global_variable(tok: &mut &Token, base_ty: &Rc<Type>, ctx: &mut Context) -> Result<()> {
    let mut first = true;
    while !tokenize::consume(tok, ";") {
        if !first {
            tokenize::expect(tok, ",", ctx)?;
        }
        first = false;
        let decl = declarator(tok, base_ty, ctx)?;
        ctx.new_gvar(&decl);
    }
    Ok(())
}

pub fn func(tok: &mut &Token, base_ty: &Rc<Type>, ctx: &mut Context) -> Result<Box<Func>> {
    ctx.stack_size = 0;
    ctx.enter_scope();
    let loc = tok.loc;
    let decl = declarator(tok, base_ty, ctx)?;
    ctx.new_gvar(&decl);
    if let TypeKind::Func { params, return_ty } = &decl.ty.kind {
        let body = compound_stmt(tok, ctx)?;
        ctx.leave_scope();
        ctx.stack_size = align_to(ctx.stack_size, 16);
        Ok(Box::new(Func {
            name: decl.name,
            return_ty: Rc::clone(&return_ty),
            params: params.clone(),
            body,
            stack_size: ctx.stack_size,
        }))
    } else {
        bail!(error_message("expected a function", ctx, loc));
    }
}

// Lookahead tokens and returns true if a given token is a start
// of a function definition or declaration.
fn is_func(tok: &mut &Token, ctx: &mut Context) -> Result<bool> {
    if tokenize::equal(tok, ";") {
        return Ok(false);
    }
    let cur = *tok;
    let dummy = Type::new_int();
    ctx.stack_size = 0;
    ctx.enter_scope();
    let decl = declarator(tok, &dummy, ctx)?;
    ctx.leave_scope();
    *tok = cur;
    Ok(decl.ty.is_func())
}

// Returns true if a given token represents a type.
fn is_typename(tok: &Token) -> bool {
    tokenize::equal(tok, "char") || tokenize::equal(tok, "int") || tokenize::equal(tok, "struct")
}

// declspec = "char" | "int" | "struct-decl
fn declspec(tok: &mut &Token, ctx: &mut Context) -> Result<Rc<Type>> {
    if tokenize::consume(tok, "char") {
        return Ok(Type::new_char());
    }
    if tokenize::equal(tok, "struct") {
        return Ok(struct_decl(tok, ctx)?);
    }
    tokenize::expect(tok, "int", ctx)?;
    Ok(Type::new_int())
}

// struct-members = "{" (declspec declarator ("," declarator)* ";")* "}"
fn struct_members(tok: &mut &Token, ctx: &mut Context) -> Result<Rc<Type>> {
    tokenize::expect(tok, "{", ctx)?;
    let mut member_decls = Vec::new();
    while !tokenize::consume(tok, "}") {
        let base_ty = declspec(tok, ctx)?;
        let mut first = true;
        while !tokenize::consume(tok, ";") {
            if !first {
                tokenize::expect(tok, ",", ctx)?;
            }
            first = false;
            let member_decl = declarator(tok, &base_ty, ctx)?;
            member_decls.push(member_decl);
        }
    }
    Ok(Type::new_struct(member_decls))
}

// struct-decl = "struct" (ident | ident? struct-members)
fn struct_decl(tok: &mut &Token, ctx: &mut Context) -> Result<Rc<Type>> {
    tokenize::expect(tok, "struct", ctx)?;
    let loc = tok.loc;
    let tag = tokenize::consume_ident(tok);
    if tag.is_some() && !tokenize::equal(tok, "{") {
        let tag = tag.unwrap();
        if let Some(ty) = ctx.find_struct_tag(tag) {
            return Ok(ty);
        }
        bail!(error_message("unknown struct type", ctx, loc));
    }
    let ty = struct_members(tok, ctx)?;
    if let Some(tag) = tag {
        ctx.new_struct_tag(tag, &ty);
    }
    Ok(ty)
}

// func-params = "(" (param ("," param)*)? ")"
// param       = declspec declarator
fn func_params(tok: &mut &Token, ctx: &mut Context) -> Result<Vec<Decl>> {
    tokenize::expect(tok, "(", ctx)?;
    let mut params = Vec::new();
    while !tokenize::consume(tok, ")") {
        if params.len() > 0 {
            tokenize::expect(tok, ",", ctx)?;
        }
        let param_base_ty = declspec(tok, ctx)?;
        let param = declarator(tok, &param_base_ty, ctx)?;
        params.push(param);
    }
    Ok(params)
}

// type-suffix = func-params
//             = "[" num "]" type-suffix
//             = ε
fn type_suffix(tok: &mut &Token, ty: &Rc<Type>, ctx: &mut Context) -> Result<Rc<Type>> {
    if tokenize::equal(tok, "(") {
        let param_decls = func_params(tok, ctx)?;
        let mut params = Vec::new();
        for param_decl in param_decls {
            let param = ctx.new_lvar(&param_decl);
            params.push(param);
        }
        Ok(Type::new_func(params, ty))
    } else if tokenize::equal(tok, "[") {
        tokenize::expect(tok, "[", ctx)?;
        let len = tokenize::expect_number(tok, ctx)?;
        tokenize::expect(tok, "]", ctx)?;
        let base_ty = type_suffix(tok, ty, ctx)?;
        Ok(Type::new_array(&base_ty, len as usize))
    } else {
        Ok(Rc::clone(ty))
    }
}

// declarator = "*"* ident type-suffix
fn declarator(tok: &mut &Token, base_ty: &Rc<Type>, ctx: &mut Context) -> Result<Decl> {
    let mut ty = Rc::clone(base_ty);
    while tokenize::consume(tok, "*") {
        ty = Type::new_ptr(&ty);
    }
    if !matches!(tok.kind, TokenKind::Ident) {
        bail!(error_message("expected an identifier", ctx, tok.loc));
    }
    if let Some(ident) = tokenize::consume_ident(tok) {
        ty = type_suffix(tok, &ty, ctx)?;
        Ok(Decl {
            name: ident.to_owned(),
            ty,
        })
    } else {
        bail!(error_message("expected an identifier", ctx, tok.loc));
    }
}

// declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
fn declaration(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    let base_ty = declspec(tok, ctx)?;
    let mut stmt_vec = Vec::new();
    let mut count = 0;
    while !tokenize::consume(tok, ";") {
        if count > 0 {
            tokenize::expect(tok, ",", ctx)?;
        }
        let loc = tok.loc;
        let decl = declarator(tok, &base_ty, ctx)?;
        let obj = ctx.new_lvar(&decl);
        if tokenize::consume(tok, "=") {
            let lhs = Expr::new_var(obj, loc);
            let rhs = assign(tok, ctx)?;
            let expr = Expr::new_assign(lhs, rhs, loc);
            let stmt = Box::new(Stmt {
                kind: StmtKind::ExprStmt(expr),
                loc,
            });
            stmt_vec.push(stmt);
        }
        count += 1;
    }
    Ok(Box::new(Stmt {
        kind: StmtKind::DeclStmt(stmt_vec),
        loc,
    }))
}

// stmt = declaration
//      | "return" expr ";"
//      | "if" "(" expr ")" stmt ("else" stmt)?
//      | "for" "(" expr-stmt? ";" expr? ";" expr? ")" stmt
//      | "while" "(" expr ")" stmt
//      | "{" block-item* "}"
//      | expr-stmt
//      | null-stmt
fn stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    if is_typename(tok) {
        Ok(declaration(tok, ctx)?)
    } else if tokenize::equal(tok, ";") {
        Ok(null_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "return") {
        Ok(return_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "{") {
        Ok(compound_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "if") {
        Ok(if_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "for") {
        Ok(for_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "while") {
        Ok(while_stmt(tok, ctx)?)
    } else {
        Ok(expr_stmt(tok, ctx)?)
    }
}

fn null_stmt(tok: &mut &Token, ctx: &Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect(tok, ";", ctx)?;
    let stmt = Stmt {
        kind: StmtKind::NullStmt,
        loc,
    };
    Ok(Box::new(stmt))
}

fn return_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect(tok, "return", ctx)?;
    let stmt = Stmt {
        kind: StmtKind::ReturnStmt(expr(tok, ctx)?),
        loc,
    };
    tokenize::expect(tok, ";", ctx)?;
    Ok(Box::new(stmt))
}

fn compound_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect(tok, "{", ctx)?;
    let mut block = Vec::new();
    ctx.enter_scope();
    while !tokenize::consume(tok, "}") {
        block.push(stmt(tok, ctx)?);
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
    tokenize::expect(tok, ";", ctx)?;
    Ok(Box::new(stmt))
}

fn if_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect(tok, "if", ctx)?;
    tokenize::expect(tok, "(", ctx)?;
    let cond = expr(tok, ctx)?;
    tokenize::expect(tok, ")", ctx)?;
    let then = stmt(tok, ctx)?;
    let mut els = None;
    if tokenize::consume(tok, "else") {
        els = Some(stmt(tok, ctx)?);
    }
    let stmt = Stmt {
        kind: StmtKind::IfStmt { cond, then, els },
        loc,
    };
    Ok(Box::new(stmt))
}

fn for_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect(tok, "for", ctx)?;
    tokenize::expect(tok, "(", ctx)?;
    let init = stmt(tok, ctx)?;
    let mut cond = None;
    if !tokenize::equal(tok, ";") {
        cond = Some(expr(tok, ctx)?);
    }
    tokenize::expect(tok, ";", ctx)?;
    let mut inc = None;
    if !tokenize::equal(tok, ")") {
        inc = Some(expr(tok, ctx)?);
    }
    tokenize::expect(tok, ")", ctx)?;
    let body = stmt(tok, ctx)?;
    let stmt = Stmt {
        kind: StmtKind::ForStmt {
            init,
            cond,
            inc,
            body,
        },
        loc,
    };
    Ok(Box::new(stmt))
}

fn while_stmt(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Stmt>> {
    let loc = tok.loc;
    tokenize::expect(tok, "while", ctx)?;
    tokenize::expect(tok, "(", ctx)?;
    let cond = expr(tok, ctx)?;
    tokenize::expect(tok, ")", ctx)?;
    let body = stmt(tok, ctx)?;
    let stmt = Stmt {
        kind: StmtKind::WhileStmt { cond, body },
        loc,
    };
    Ok(Box::new(stmt))
}

// expr = assign ("," expr)?
fn expr(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let lhs = assign(tok, ctx)?;
    if tokenize::equal(tok, ",") {
        let loc = tok.loc;
        tokenize::consume(tok, ",");
        let rhs = expr(tok, ctx)?;
        return Ok(Expr::new_binary(BinaryOp::COMMA, lhs, rhs, ctx, loc)?);
    }
    Ok(lhs)
}

// assign = equality ("=" assign)?
fn assign(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let lhs = equality(tok, ctx)?;
    let loc = tok.loc;
    if tokenize::consume(tok, "=") {
        let rhs = assign(tok, ctx)?;
        Ok(Expr::new_assign(lhs, rhs, loc))
    } else {
        Ok(lhs)
    }
}

// equality = relational ("==" relational | "!=" relational)*
fn equality(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = relational(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume(tok, "==") {
            expr = Expr::new_binary(BinaryOp::EQ, expr, relational(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume(tok, "!=") {
            expr = Expr::new_binary(BinaryOp::NE, expr, relational(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
fn relational(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = add(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume(tok, "<") {
            expr = Expr::new_binary(BinaryOp::LT, expr, add(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume(tok, "<=") {
            expr = Expr::new_binary(BinaryOp::LE, expr, add(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume(tok, ">") {
            expr = Expr::new_binary(BinaryOp::LT, add(tok, ctx)?, expr, ctx, loc)?;
            continue;
        }
        if tokenize::consume(tok, ">=") {
            expr = Expr::new_binary(BinaryOp::LE, add(tok, ctx)?, expr, ctx, loc)?;
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
        if tokenize::consume(tok, "+") {
            let rhs = mul(tok, ctx)?;
            expr = Expr::new_binary(BinaryOp::ADD, expr, rhs, ctx, loc)?;
            continue;
        }
        if tokenize::consume(tok, "-") {
            let rhs = mul(tok, ctx)?;
            expr = Expr::new_binary(BinaryOp::SUB, expr, rhs, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// mul = unary ("*" unary | "/" unary)*
fn mul(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut expr = unary(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume(tok, "*") {
            expr = Expr::new_binary(BinaryOp::MUL, expr, unary(tok, ctx)?, ctx, loc)?;
            continue;
        }
        if tokenize::consume(tok, "/") {
            expr = Expr::new_binary(BinaryOp::DIV, expr, unary(tok, ctx)?, ctx, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// unary = ("+" | "-" | "*" | "&") unary
//       | postfix
fn unary(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let loc = tok.loc;
    if tokenize::consume(tok, "+") {
        unary(tok, ctx)
    } else if tokenize::consume(tok, "-") {
        Ok(Expr::new_unary(UnaryOp::NEG, unary(tok, ctx)?, ctx, loc)?)
    } else if tokenize::consume(tok, "*") {
        Ok(Expr::new_unary(UnaryOp::DEREF, unary(tok, ctx)?, ctx, loc)?)
    } else if tokenize::consume(tok, "&") {
        Ok(Expr::new_unary(UnaryOp::ADDR, unary(tok, ctx)?, ctx, loc)?)
    } else {
        postfix(tok, ctx)
    }
}

// postfix = primary ("[" expr "]" | "." ident | "->" ident)*
fn postfix(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let mut ret = primary(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume(tok, "[") {
            let index = expr(tok, ctx)?;
            tokenize::expect(tok, "]", ctx)?;
            ret = Expr::new_unary(
                UnaryOp::DEREF,
                Expr::new_binary(BinaryOp::ADD, ret, index, ctx, loc)?,
                ctx,
                loc,
            )?;
        } else if tokenize::consume(tok, ".") {
            let name = tokenize::expect_ident(tok, ctx)?;
            ret = Expr::new_member(ret, name, ctx, loc)?;
        } else if tokenize::consume(tok, "->") {
            ret = Expr::new_unary(UnaryOp::DEREF, ret, ctx, loc)?;
            let name = tokenize::expect_ident(tok, ctx)?;
            ret = Expr::new_member(ret, name, ctx, loc)?;
        } else {
            break;
        }
    }
    Ok(ret)
}

fn stmt_expr(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let loc = tok.loc;
    let stmt = compound_stmt(tok, ctx)?;
    if let StmtKind::CompoundStmt(stmt_vec) = stmt.kind {
        if stmt_vec.is_empty() {
            bail!(error_message(
                "statement expression returning void is not supported",
                ctx,
                loc
            ));
        }
        if let StmtKind::ExprStmt(expr) = &stmt_vec.last().unwrap().kind {
            let ty = Rc::clone(&expr.ty);
            let expr = Expr {
                kind: ExprKind::StmtExpr(stmt_vec),
                ty,
                loc,
            };
            return Ok(Box::new(expr));
        } else {
            bail!(error_message(
                "statement expression returning void is not supported",
                ctx,
                loc
            ));
        }
    } else {
        unreachable!();
    }
}

// primary = "(" "{" stmt+ "}" ")"
//         | "(" expr ")"
//         | "sizeof" unary
//         | ident func-args?
//         | str
//         | num
//
// func-args = "(" (expr ("," expr)*)? ")"
fn primary(tok: &mut &Token, ctx: &mut Context) -> Result<Box<Expr>> {
    let loc = tok.loc;

    if tokenize::consume(tok, "(") {
        let inner;
        if tokenize::equal(tok, "{") {
            inner = stmt_expr(tok, ctx)?;
        } else {
            inner = expr(tok, ctx)?
        }
        tokenize::expect(tok, ")", ctx)?;
        return Ok(inner);
    }

    if tokenize::consume(tok, "sizeof") {
        let expr = unary(tok, ctx)?;
        return Ok(Expr::new_num(expr.ty.size as i32, loc));
    }

    if let Some(val) = tokenize::consume_number(tok) {
        return Ok(Expr::new_num(val, loc));
    }

    if let Some(ident) = tokenize::consume_ident(tok) {
        // Function call
        if tokenize::consume(tok, "(") {
            let mut args = Vec::new();
            while !tokenize::consume(tok, ")") {
                if args.len() > 0 {
                    tokenize::expect(tok, ",", ctx)?;
                }
                args.push(assign(tok, ctx)?);
            }
            return Ok(Expr::new_funcall(ident, args, loc));
        }
        // Variable
        if let Some(obj) = ctx.find_var(&ident) {
            return Ok(Expr::new_var(obj, loc));
        } else {
            bail!(error_message("undefined variable", ctx, loc));
        }
    }

    if let Some(bytes) = tokenize::consume_str(tok) {
        let obj = ctx.new_str(bytes.clone());
        return Ok(Expr::new_var(obj, loc));
    }

    bail!(error_message("expected an expression", ctx, loc))
}
