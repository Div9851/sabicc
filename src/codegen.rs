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

fn push() {
    println!("  push rax");
}

fn pop(reg: &str) {
    println!("  pop {}", reg);
}

// Store rax to an address that the stack top is pointing to.
fn store(ty: &Type) {
    pop("rdi");

    if ty.size == 1 {
        println!("  mov [rdi], al");
    } else {
        println!("  mov [rdi], rax");
    }
}

// Compute the absolute address to a given node.
// It's an error if a given node does not reside in memory.
fn gen_addr(expr: &Expr, ctx: &mut Context) -> Result<()> {
    if let ExprKind::Var(obj) = &expr.kind {
        match &obj.kind {
            ObjKind::Local(offset) => {
                println!("  lea rax, [rbp-{}]", offset);
            }
            ObjKind::Global(name) => {
                println!("  lea rax, {}[rip]", name);
            }
        }
        return Ok(());
    }
    if let ExprKind::Unary {
        op: UnaryOp::DEREF,
        expr,
    } = &expr.kind
    {
        gen_expr(expr, ctx)?;
        return Ok(());
    }
    bail!(error_message("not an lvalue", ctx, expr.loc));
}

fn load(ty: &Type) {
    // If it is an array, do not attempt to load a value to the
    // register because in general we can't load an entire array to a
    // register. As a result, the result of an evaluation of an array
    // becomes not the array itself but the address of the array.
    // This is where "array is automatically converted to a pointer to
    // the first element of the array in C" occurs.
    if let TypeKind::Array(_, _) = ty.kind {
        return;
    }

    if ty.size == 1 {
        println!("  movsbq rax, [rax]");
    } else {
        println!("  mov rax, [rax]");
    }
}

pub fn gen_program(program: &mut Program) -> Result<()> {
    println!(".intel_syntax noprefix");
    let globals = program.ctx.scopes.first().unwrap();
    for (_, obj) in globals {
        emit_data(obj, &program.ctx)?;
    }
    let funcs = &program.funcs;
    for func in funcs {
        emit_text(func, &mut program.ctx)?;
    }
    Ok(())
}

fn emit_data(obj: &Obj, ctx: &Context) -> Result<()> {
    if let ObjKind::Global(name) = &obj.kind {
        if !obj.ty.is_func() {
            println!(".data");
            println!(".globl {}", name);
            println!("{}:", name);
            if let Some(bytes) = ctx.init_data.get(name) {
                for b in bytes {
                    println!("  .byte {}", b);
                }
                println!("  .byte 0");
            } else {
                println!("  .zero {}", obj.ty.size);
            }
        }
    }
    Ok(())
}

fn emit_text(func: &Func, ctx: &mut Context) -> Result<()> {
    println!(".globl {}", func.name);
    println!(".text");
    println!("{}:", func.name);
    // Prologue
    println!("  push rbp");
    println!("  mov rbp, rsp");
    println!("  sub rsp, {}", align_to(func.stack_size, 16));
    // Save passed-by-register arguments to the stack
    let mut nargs = 0;
    for obj in &func.params {
        if let ObjKind::Local(offset) = obj.kind {
            if obj.ty.size == 1 {
                println!("  mov [rbp-{}], {}", offset, ARGREG8[nargs]);
            } else {
                println!("  mov [rbp-{}], {}", offset, ARGREG64[nargs]);
            }
        } else {
            unreachable!();
        }
        nargs += 1;
    }
    // Body
    gen_stmt(&func.body, ctx)?;
    // Epilogue
    println!("  mov rsp, rbp");
    println!("  pop rbp");
    println!("  ret");
    Ok(())
}

fn gen_stmt(stmt: &Stmt, ctx: &mut Context) -> Result<()> {
    match &stmt.kind {
        StmtKind::DeclStmt(stmt_vec) => {
            for stmt in stmt_vec {
                gen_stmt(stmt, ctx)?;
            }
            Ok(())
        }
        StmtKind::NullStmt => Ok(()),
        StmtKind::ExprStmt(expr) => {
            gen_expr(expr, ctx)?;
            Ok(())
        }
        StmtKind::ReturnStmt(expr) => {
            gen_expr(&expr, ctx)?;
            println!("  mov rsp, rbp");
            println!("  pop rbp");
            println!("  ret");
            Ok(())
        }
        StmtKind::CompoundStmt(stmt_vec) => {
            for stmt in stmt_vec {
                gen_stmt(stmt, ctx)?;
            }
            Ok(())
        }
        StmtKind::IfStmt { cond, then, els } => {
            gen_expr(&cond, ctx)?;
            println!("  cmp rax, 0");
            println!("  je .L.else.{}", ctx.id);
            gen_stmt(then, ctx)?;
            println!("  jmp .L.end.{}", ctx.id);
            println!(".L.else.{}:", ctx.id);
            if let Some(els) = els {
                gen_stmt(els, ctx)?;
            }
            println!(".L.end.{}:", ctx.id);
            ctx.id += 1;
            Ok(())
        }
        StmtKind::ForStmt {
            init,
            cond,
            inc,
            body,
        } => {
            gen_stmt(init, ctx)?;
            println!(".L.begin.{}:", ctx.id);
            if let Some(cond) = cond {
                gen_expr(cond, ctx)?;
                println!("  cmp rax, 0");
                println!("  je .L.end.{}", ctx.id);
            }
            gen_stmt(body, ctx)?;
            if let Some(inc) = inc {
                gen_expr(inc, ctx)?;
            }
            println!("  jmp .L.begin.{}", ctx.id);
            println!(".L.end.{}:", ctx.id);
            ctx.id += 1;
            Ok(())
        }
        StmtKind::WhileStmt { cond, body } => {
            println!(".L.begin.{}:", ctx.id);
            gen_expr(cond, ctx)?;
            println!("  cmp rax, 0");
            println!("  je .L.end.{}", ctx.id);
            gen_stmt(body, ctx)?;
            println!("  jmp .L.begin.{}", ctx.id);
            println!(".L.end.{}:", ctx.id);
            ctx.id += 1;
            Ok(())
        }
    }
}

// Generate code for a given node.
fn gen_expr(expr: &Expr, ctx: &mut Context) -> Result<()> {
    match &expr.kind {
        ExprKind::StmtExpr(stmt_vec) => {
            for stmt in stmt_vec {
                gen_stmt(stmt, ctx)?;
            }
        }
        ExprKind::Assign { lhs, rhs } => {
            gen_addr(&lhs, ctx)?;
            push();
            gen_expr(&rhs, ctx)?;
            store(&expr.ty);
        }
        ExprKind::Binary { op, lhs, rhs } => {
            gen_expr(&rhs, ctx)?;
            push();
            gen_expr(&lhs, ctx)?;
            pop("rdi");
            match op {
                BinaryOp::ADD => {
                    println!("  add rax, rdi");
                }
                BinaryOp::SUB => {
                    println!("  sub rax, rdi");
                }
                BinaryOp::MUL => {
                    println!("  imul rax, rdi");
                }
                BinaryOp::DIV => {
                    println!("  cqo");
                    println!("  idiv rdi");
                }
                BinaryOp::EQ => {
                    println!("  cmp rax, rdi");
                    println!("  sete al");
                    println!("  movzb rax, al");
                }
                BinaryOp::NE => {
                    println!("  cmp rax, rdi");
                    println!("  setne al");
                    println!("  movzb rax, al");
                }
                BinaryOp::LT => {
                    println!("  cmp rax, rdi");
                    println!("  setl al");
                    println!("  movzb rax, al");
                }
                BinaryOp::LE => {
                    println!("  cmp rax, rdi");
                    println!("  setle al");
                    println!("  movzb rax, al");
                }
            };
        }
        ExprKind::Unary { op, expr: operand } => {
            match op {
                UnaryOp::NEG => {
                    gen_expr(&operand, ctx)?;
                    println!("  neg rax");
                }
                UnaryOp::DEREF => {
                    gen_expr(&operand, ctx)?;
                    load(&expr.ty);
                }
                UnaryOp::ADDR => {
                    gen_addr(&operand, ctx)?;
                }
            };
        }
        ExprKind::Var(_) => {
            gen_addr(expr, ctx)?;
            load(&expr.ty);
        }
        ExprKind::Num(val) => {
            println!("  mov rax, {}", val);
        }
        ExprKind::FunCall { name, args } => {
            let argreg = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
            let mut nargs = 0;
            for arg in args {
                gen_expr(arg, ctx)?;
                push();
                nargs += 1;
            }
            for i in (0..nargs).rev() {
                pop(argreg[i]);
            }
            // todo: RSP must be align to 16
            println!("  call {}", name);
        }
    };
    Ok(())
}
