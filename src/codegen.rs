use crate::parse::{BinaryOp, Expr, ExprKind, Func, Program, Stmt, StmtKind, UnaryOp};
use crate::{error_message, Context, Obj, ObjKind, Type, TypeKind};

use anyhow::{bail, Result};
use std::unreachable;

static ARGREG64: [&'static str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
static ARGREG8: [&'static str; 6] = ["dil", "sil", "dl", "cl", "r8b", "r9b"];

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to(5, 8) returns 8 and align_to(11, 8) returns 16.
fn align_to(n: usize, align: usize) -> usize {
    (n + align - 1) / align * align
}

fn push() -> String {
    "  push rax\n".to_owned()
}

fn pop(reg: &str) -> String {
    format!("  pop {}\n", reg)
}

// Store rax to an address that the stack top is pointing to.
fn store(ty: &Type) -> String {
    let mut text = String::new();
    text += &pop("rdi");

    if ty.size == 1 {
        text += "  mov [rdi], al\n";
    } else {
        text += "  mov [rdi], rax\n";
    }
    text
}

// Compute the absolute address to a given node.
// It's an error if a given node does not reside in memory.
fn gen_addr(expr: &Expr, ctx: &mut Context) -> Result<String> {
    let mut text = String::new();
    if let ExprKind::Var(obj) = &expr.kind {
        match &obj.kind {
            ObjKind::Local(offset) => {
                text += &format!("  lea rax, [rbp-{}]\n", offset);
            }
            ObjKind::Global(name) => {
                text += &format!("  lea rax, {}[rip]\n", name);
            }
        }
        return Ok(text);
    }
    if let ExprKind::Unary {
        op: UnaryOp::DEREF,
        expr,
    } = &expr.kind
    {
        text += &gen_expr(expr, ctx)?;
        return Ok(text);
    }
    bail!(error_message("not an lvalue", ctx, expr.loc));
}

fn load(ty: &Type) -> String {
    // If it is an array, do not attempt to load a value to the
    // register because in general we can't load an entire array to a
    // register. As a result, the result of an evaluation of an array
    // becomes not the array itself but the address of the array.
    // This is where "array is automatically converted to a pointer to
    // the first element of the array in C" occurs.
    if let TypeKind::Array(_, _) = ty.kind {
        return "".to_owned();
    }

    if ty.size == 1 {
        "  movsbq rax, [rax]\n".to_owned()
    } else {
        "  mov rax, [rax]\n".to_owned()
    }
}

pub fn gen_program(program: &mut Program) -> Result<String> {
    let mut text = String::new();
    text += ".intel_syntax noprefix\n";
    let globals = program.ctx.scopes.first().unwrap();
    for (_, obj) in globals {
        text += &emit_data(obj, &program.ctx)?;
    }
    let funcs = &program.funcs;
    for func in funcs {
        text += &emit_text(func, &mut program.ctx)?;
    }
    Ok(text)
}

fn emit_data(obj: &Obj, ctx: &Context) -> Result<String> {
    let mut text = String::new();
    if let ObjKind::Global(name) = &obj.kind {
        if !obj.ty.is_func() {
            text += ".data\n";
            text += &format!(".globl {}\n", name);
            text += &format!("{}:\n", name);
            if let Some(bytes) = ctx.init_data.get(name) {
                for b in bytes {
                    text += &format!("  .byte {}\n", b);
                }
                text += "  .byte 0\n";
            } else {
                text += &format!("  .zero {}\n", obj.ty.size);
            }
        }
    }
    Ok(text)
}

fn emit_text(func: &Func, ctx: &mut Context) -> Result<String> {
    let mut text = String::new();
    text += &format!(".globl {}\n", func.name);
    text += &format!(".text\n");
    text += &format!("{}:\n", func.name);
    // Prologue
    text += "  push rbp\n";
    text += "  mov rbp, rsp\n";
    text += &format!("  sub rsp, {}\n", align_to(func.stack_size, 16));
    // Save passed-by-register arguments to the stack
    let mut nargs = 0;
    for obj in &func.params {
        if let ObjKind::Local(offset) = obj.kind {
            if obj.ty.size == 1 {
                text += &format!("  mov [rbp-{}], {}\n", offset, ARGREG8[nargs]);
            } else {
                text += &format!("  mov [rbp-{}], {}\n", offset, ARGREG64[nargs]);
            }
        } else {
            unreachable!();
        }
        nargs += 1;
    }
    // Body
    text += &gen_stmt(&func.body, ctx)?;
    // Epilogue
    text += "  mov rsp, rbp\n";
    text += "  pop rbp\n";
    text += "  ret\n";
    Ok(text)
}

fn gen_stmt(stmt: &Stmt, ctx: &mut Context) -> Result<String> {
    let mut text = String::new();
    match &stmt.kind {
        StmtKind::DeclStmt(stmt_vec) => {
            for stmt in stmt_vec {
                text += &gen_stmt(stmt, ctx)?;
            }
            Ok(text)
        }
        StmtKind::NullStmt => Ok(text),
        StmtKind::ExprStmt(expr) => {
            text += &gen_expr(expr, ctx)?;
            Ok(text)
        }
        StmtKind::ReturnStmt(expr) => {
            text += &gen_expr(&expr, ctx)?;
            text += "  mov rsp, rbp\n";
            text += "  pop rbp\n";
            text += "  ret\n";
            Ok(text)
        }
        StmtKind::CompoundStmt(stmt_vec) => {
            for stmt in stmt_vec {
                text += &gen_stmt(stmt, ctx)?;
            }
            Ok(text)
        }
        StmtKind::IfStmt { cond, then, els } => {
            text += &gen_expr(&cond, ctx)?;
            text += "  cmp rax, 0\n";
            text += &format!("  je .L.else.{}\n", ctx.id);
            text += &gen_stmt(then, ctx)?;
            text += &format!("  jmp .L.end.{}\n", ctx.id);
            text += &format!(".L.else.{}:\n", ctx.id);
            if let Some(els) = els {
                text += &gen_stmt(els, ctx)?;
            }
            text += &format!(".L.end.{}:\n", ctx.id);
            ctx.id += 1;
            Ok(text)
        }
        StmtKind::ForStmt {
            init,
            cond,
            inc,
            body,
        } => {
            text += &gen_stmt(init, ctx)?;
            text += &format!(".L.begin.{}:\n", ctx.id);
            if let Some(cond) = cond {
                text += &gen_expr(cond, ctx)?;
                text += "  cmp rax, 0\n";
                text += &format!("  je .L.end.{}\n", ctx.id);
            }
            text += &gen_stmt(body, ctx)?;
            if let Some(inc) = inc {
                text += &gen_expr(inc, ctx)?;
            }
            text += &format!("  jmp .L.begin.{}\n", ctx.id);
            text += &format!(".L.end.{}:\n", ctx.id);
            ctx.id += 1;
            Ok(text)
        }
        StmtKind::WhileStmt { cond, body } => {
            text += &format!(".L.begin.{}:\n", ctx.id);
            text += &gen_expr(cond, ctx)?;
            text += "  cmp rax, 0\n";
            text += &format!("  je .L.end.{}\n", ctx.id);
            text += &gen_stmt(body, ctx)?;
            text += &format!("  jmp .L.begin.{}\n", ctx.id);
            text += &format!(".L.end.{}:\n", ctx.id);
            ctx.id += 1;
            Ok(text)
        }
    }
}

// Generate text for a given node.
fn gen_expr(expr: &Expr, ctx: &mut Context) -> Result<String> {
    let mut text = String::new();
    match &expr.kind {
        ExprKind::StmtExpr(stmt_vec) => {
            for stmt in stmt_vec {
                text += &gen_stmt(stmt, ctx)?;
            }
        }
        ExprKind::Assign { lhs, rhs } => {
            text += &gen_addr(&lhs, ctx)?;
            text += &push();
            text += &gen_expr(&rhs, ctx)?;
            text += &store(&expr.ty);
        }
        ExprKind::Binary { op, lhs, rhs } => {
            text += &gen_expr(&rhs, ctx)?;
            text += &push();
            text += &gen_expr(&lhs, ctx)?;
            text += &pop("rdi");
            match op {
                BinaryOp::ADD => {
                    text += "  add rax, rdi\n";
                }
                BinaryOp::SUB => {
                    text += "  sub rax, rdi\n";
                }
                BinaryOp::MUL => {
                    text += "  imul rax, rdi\n";
                }
                BinaryOp::DIV => {
                    text += "  cqo\n";
                    text += "  idiv rdi\n";
                }
                BinaryOp::EQ => {
                    text += "  cmp rax, rdi\n";
                    text += "  sete al\n";
                    text += "  movzb rax, al\n";
                }
                BinaryOp::NE => {
                    text += "  cmp rax, rdi\n";
                    text += "  setne al\n";
                    text += "  movzb rax, al\n";
                }
                BinaryOp::LT => {
                    text += "  cmp rax, rdi\n";
                    text += "  setl al\n";
                    text += "  movzb rax, al\n";
                }
                BinaryOp::LE => {
                    text += "  cmp rax, rdi\n";
                    text += "  setle al\n";
                    text += "  movzb rax, al\n";
                }
            };
        }
        ExprKind::Unary { op, expr: operand } => {
            match op {
                UnaryOp::NEG => {
                    text += &gen_expr(&operand, ctx)?;
                    text += "  neg rax\n";
                }
                UnaryOp::DEREF => {
                    text += &gen_expr(&operand, ctx)?;
                    text += &load(&expr.ty);
                }
                UnaryOp::ADDR => {
                    text += &gen_addr(&operand, ctx)?;
                }
            };
        }
        ExprKind::Var(_) => {
            text += &gen_addr(expr, ctx)?;
            text += &load(&expr.ty);
        }
        ExprKind::Num(val) => {
            text += &format!("  mov rax, {}\n", val);
        }
        ExprKind::FunCall { name, args } => {
            let argreg = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
            let mut nargs = 0;
            for arg in args {
                text += &gen_expr(arg, ctx)?;
                text += &push();
                nargs += 1;
            }
            for i in (0..nargs).rev() {
                text += &pop(argreg[i]);
            }
            // todo: RSP must be align to 16
            text += &format!("  call {}\n", name);
        }
    };
    Ok(text)
}
