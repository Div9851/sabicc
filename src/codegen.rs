use crate::parse::{BinaryOp, Expr, ExprKind, Func, Program, Stmt, StmtKind, UnaryOp};
use crate::{error_message, Context, Obj, ObjKind, Type, TypeKind};

use anyhow::{bail, Result};
use std::unreachable;

static ARGREG64: [&'static str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
static ARGREG32: [&'static str; 6] = ["edi", "esi", "edx", "ecx", "r8d", "r9d"];
static ARGREG16: [&'static str; 6] = ["di", "si", "dx", "cx", "r8w", "r9w"];
static ARGREG8: [&'static str; 6] = ["dil", "sil", "dl", "cl", "r8b", "r9b"];

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

    if ty.is_struct() || ty.is_union() {
        for i in 0..ty.size {
            text += &format!("  mov r8b, [rax+{}]\n", i);
            text += &format!("  mov [rdi+{}], r8b\n", i);
        }
        return text;
    }

    if ty.size == 1 {
        text += "  mov [rdi], al\n";
    } else if ty.size == 2 {
        text += "  mov [rdi], ax\n";
    } else if ty.size == 4 {
        text += "   mov [rdi], eax\n";
    } else {
        text += "  mov [rdi], rax\n";
    }
    text
}

// Compute the absolute address to a given node.
// It's an error if a given node does not reside in memory.
fn gen_addr(expr: &Expr, ctx: &mut Context) -> Result<String> {
    let mut text = String::new();
    match &expr.kind {
        ExprKind::Var(obj) => {
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
        ExprKind::Unary {
            op: UnaryOp::DEREF,
            expr,
        } => {
            text += &gen_expr(expr, ctx)?;
            return Ok(text);
        }
        ExprKind::Binary {
            op: BinaryOp::COMMA,
            lhs,
            rhs,
        } => {
            text += &gen_expr(lhs, ctx)?;
            text += &gen_addr(rhs, ctx)?;
            return Ok(text);
        }
        ExprKind::Member { expr, offset } => {
            text += &gen_addr(expr, ctx)?;
            text += &format!("  add rax, {}\n", offset);
            return Ok(text);
        }
        _ => bail!(error_message("not an lvalue", ctx, expr.loc)),
    }
}

fn load(ty: &Type) -> String {
    if let TypeKind::Array(_, _) | TypeKind::Struct(_) | TypeKind::Union(_) = ty.kind {
        // If it is an array, do not attempt to load a value to the
        // register because in general we can't load an entire array to a
        // register. As a result, the result of an evaluation of an array
        // becomes not the array itself but the address of the array.
        // This is where "array is automatically converted to a pointer to
        // the first element of the array in C" occurs.
        return "".to_owned();
    }

    if ty.size == 1 {
        "  movsbq rax, [rax]\n".to_owned()
    } else if ty.size == 2 {
        "  movswq rax, [rax]\n".to_owned()
    } else if ty.size == 4 {
        "   movsxd rax, [rax]\n".to_owned()
    } else {
        "  mov rax, [rax]\n".to_owned()
    }
}

pub fn gen_program(program: &mut Program) -> Result<String> {
    let mut text = String::new();
    text += &format!(".file 1 \"{}\"\n", program.ctx.filename);
    text += ".intel_syntax noprefix\n";
    let globals = program.ctx.scopes.first().unwrap();
    for (_, obj) in globals {
        text += &emit_data(obj, &program.ctx)?;
    }
    let functions = &program.functions;
    for func in functions {
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

fn store_gp(r: usize, offset: usize, sz: usize) -> String {
    if sz == 1 {
        format!("  mov [rbp-{}], {}\n", offset, ARGREG8[r])
    } else if sz == 2 {
        format!("  mov [rbp-{}], {}\n", offset, ARGREG16[r])
    } else if sz == 4 {
        format!("  mov [rbp-{}], {}\n", offset, ARGREG32[r])
    } else if sz == 8 {
        format!("  mov [rbp-{}], {}\n", offset, ARGREG64[r])
    } else {
        unreachable!();
    }
}

fn emit_text(func: &Func, ctx: &mut Context) -> Result<String> {
    let mut text = String::new();
    text += &format!(".globl {}\n", func.name);
    text += &format!(".text\n");
    text += &format!("{}:\n", func.name);
    // Prologue
    text += "  push rbp\n";
    text += "  mov rbp, rsp\n";
    text += &format!("  sub rsp, {}\n", func.stack_size);
    // Save passed-by-register arguments to the stack
    for (r, obj) in func.params.iter().enumerate() {
        if let ObjKind::Local(offset) = obj.kind {
            text += &store_gp(r, offset, obj.ty.size);
        } else {
            unreachable!();
        }
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
    text += &format!("  .loc 1 {}\n", ctx.line_no[stmt.loc] + 1);
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
    text += &format!("  .loc 1 {}\n", ctx.line_no[expr.loc] + 1);
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
        ExprKind::Binary {
            op: BinaryOp::COMMA,
            lhs,
            rhs,
        } => {
            text += &gen_expr(&lhs, ctx)?;
            text += &gen_expr(&rhs, ctx)?;
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
                BinaryOp::COMMA => {}
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
        ExprKind::Member { expr: _, offset: _ } => {
            text += &gen_addr(expr, ctx)?;
            text += &load(&expr.ty);
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
