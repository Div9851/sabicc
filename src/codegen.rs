use crate::{
    error::Error,
    parse::{
        BinaryOp, Expr, ExprKind, Func, Obj, ObjKind, Program, Stmt, StmtKind, Type, TypeKind,
        UnaryOp,
    },
};
use std::unreachable;

static ARGREG64: [&'static str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
static ARGREG8: [&'static str; 6] = ["dil", "sil", "dl", "cl", "r8b", "r9b"];

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to(5, 8) returns 8 and align_to(11, 8) returns 16.
fn align_to(n: usize, align: usize) -> usize {
    (n + align - 1) / align * align
}

pub struct CodegenContext {
    pub label: usize,
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
fn gen_addr(expr: &Expr) -> Result<(), Error> {
    if let ExprKind::Var(obj) = &expr.kind {
        match &obj.kind {
            ObjKind::Local(offset) => {
                println!("  lea rax, [rbp-{}]", offset);
            }
            ObjKind::Global(label) => {
                println!("  lea rax, {}[rip]", label);
            }
        }
        return Ok(());
    }
    if let ExprKind::Unary {
        op: UnaryOp::DEREF,
        expr,
    } = &expr.kind
    {
        gen_expr(expr)?;
        return Ok(());
    }
    Err(Error {
        loc: expr.loc,
        msg: "not an lvalue".to_owned(),
    })
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

pub fn gen_program(program: &Program) -> Result<(), Error> {
    println!(".intel_syntax noprefix");
    let globals = program.ctx.scopes.first().unwrap();
    for (_, obj) in globals {
        emit_data(obj)?;
    }
    let funcs = &program.funcs;
    let mut ctx = &mut CodegenContext { label: 0 };
    for f in funcs {
        emit_text(f, &mut ctx)?;
    }
    Ok(())
}

fn emit_data(obj: &Obj) -> Result<(), Error> {
    if let ObjKind::Global(name) = &obj.kind {
        if !obj.ty.is_func() {
            println!(".data");
            println!(".globl {}", name);
            println!("{}:", name);
            println!("  .zero {}", obj.ty.size);
        }
    }
    Ok(())
}

fn emit_text(func: &Func, ctx: &mut CodegenContext) -> Result<(), Error> {
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

fn gen_stmt(stmt: &Stmt, ctx: &mut CodegenContext) -> Result<(), Error> {
    match &stmt.kind {
        StmtKind::DeclStmt(stmt_vec) => {
            for stmt in stmt_vec {
                gen_stmt(stmt, ctx)?;
            }
            Ok(())
        }
        StmtKind::NullStmt => Ok(()),
        StmtKind::ExprStmt(expr) => {
            gen_expr(expr)?;
            Ok(())
        }
        StmtKind::ReturnStmt(expr) => {
            gen_expr(&expr)?;
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
            gen_expr(&cond)?;
            println!("  cmp rax, 0");
            println!("  je .L.else.{}", ctx.label);
            gen_stmt(then, ctx)?;
            println!("  jmp .L.end.{}", ctx.label);
            println!(".L.else.{}:", ctx.label);
            if let Some(els) = els {
                gen_stmt(els, ctx)?;
            }
            println!(".L.end.{}:", ctx.label);
            ctx.label += 1;
            Ok(())
        }
        StmtKind::ForStmt {
            init,
            cond,
            inc,
            body,
        } => {
            gen_stmt(init, ctx)?;
            println!(".L.begin.{}:", ctx.label);
            if let Some(cond) = cond {
                gen_expr(cond)?;
                println!("  cmp rax, 0");
                println!("  je .L.end.{}", ctx.label);
            }
            gen_stmt(body, ctx)?;
            if let Some(inc) = inc {
                gen_expr(inc)?;
            }
            println!("  jmp .L.begin.{}", ctx.label);
            println!(".L.end.{}:", ctx.label);
            ctx.label += 1;
            Ok(())
        }
        StmtKind::WhileStmt { cond, body } => {
            println!(".L.begin.{}:", ctx.label);
            gen_expr(cond)?;
            println!("  cmp rax, 0");
            println!("  je .L.end.{}", ctx.label);
            gen_stmt(body, ctx)?;
            println!("  jmp .L.begin.{}", ctx.label);
            println!(".L.end.{}:", ctx.label);
            ctx.label += 1;
            Ok(())
        }
    }
}

// Generate code for a given node.
fn gen_expr(expr: &Expr) -> Result<(), Error> {
    match &expr.kind {
        ExprKind::Assign { lhs, rhs } => {
            gen_addr(&lhs)?;
            push();
            gen_expr(&rhs)?;
            store(&expr.ty);
        }
        ExprKind::Binary { op, lhs, rhs } => {
            gen_expr(&rhs)?;
            push();
            gen_expr(&lhs)?;
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
                    gen_expr(&operand)?;
                    println!("  neg rax");
                }
                UnaryOp::DEREF => {
                    gen_expr(&operand)?;
                    load(&expr.ty);
                }
                UnaryOp::ADDR => {
                    gen_addr(&operand)?;
                }
            };
        }
        ExprKind::Var(_) => {
            gen_addr(expr)?;
            load(&expr.ty);
        }
        ExprKind::Num(val) => {
            println!("  mov rax, {}", val);
        }
        ExprKind::FunCall { name, args } => {
            let argreg = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
            let mut nargs = 0;
            for arg in args {
                gen_expr(arg)?;
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
