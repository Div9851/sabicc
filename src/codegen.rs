use crate::parse::{BinaryOp, Expr, ExprKind, Func, Program, Stmt, StmtKind, UnaryOp};
use crate::{error_message, Context, Obj, ObjKind, Type, TypeKind};

use anyhow::Result;
use std::cell::RefCell;
use std::fmt::Write;
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
fn store(ty: &RefCell<Type>) -> String {
    let mut output = String::new();
    write!(&mut output, "{}", pop("rdi")).unwrap();

    let size = ty.borrow().size.unwrap();
    if ty.borrow().is_struct() || ty.borrow().is_union() {
        for i in 0..size {
            writeln!(&mut output, "  mov r8b, [rax+{}]", i).unwrap();
            writeln!(&mut output, "  mov [rdi+{}], r8b", i).unwrap();
        }
        return output;
    }

    if size == 1 {
        writeln!(&mut output, "  mov [rdi], al").unwrap();
    } else if size == 2 {
        writeln!(&mut output, "  mov [rdi], ax").unwrap();
    } else if size == 4 {
        writeln!(&mut output, "  mov [rdi], eax").unwrap();
    } else {
        writeln!(&mut output, "  mov [rdi], rax").unwrap();
    }
    output
}

// Compute the absolute address to a given node.
// It's an error if a given node does not reside in memory.
fn gen_addr(expr: &Expr, ctx: &mut Context) -> Result<String> {
    let mut output = String::new();
    match &expr.kind {
        ExprKind::Var(obj) => {
            match &obj.kind {
                ObjKind::Local(offset) => {
                    writeln!(&mut output, "  lea rax, [rbp-{}]", offset).unwrap();
                }
                ObjKind::Global(name) => {
                    writeln!(&mut output, "  lea rax, {}[rip]", name).unwrap();
                }
                _ => {
                    unreachable!();
                }
            }
            Ok(output)
        }
        ExprKind::Unary {
            op: UnaryOp::DEREF,
            expr,
        } => {
            write!(&mut output, "{}", gen_expr(expr, ctx)?).unwrap();
            Ok(output)
        }
        ExprKind::Binary {
            op: BinaryOp::COMMA,
            lhs,
            rhs,
        } => {
            write!(&mut output, "{}", gen_expr(lhs, ctx)?).unwrap();
            write!(&mut output, "{}", gen_addr(rhs, ctx)?).unwrap();
            Ok(output)
        }
        ExprKind::Member { expr, offset } => {
            write!(&mut output, "{}", gen_addr(expr, ctx)?).unwrap();
            writeln!(&mut output, "  add rax, {}", offset).unwrap();
            Ok(output)
        }
        _ => Err(error_message("not an lvalue", ctx, expr.loc)),
    }
}

fn load(ty: &RefCell<Type>) -> String {
    let mut output = String::new();
    if let TypeKind::Array(_, _) | TypeKind::Struct(_) | TypeKind::Union(_) = ty.borrow().kind {
        // If it is an array, do not attempt to load a value to the
        // register because in general we can't load an entire array to a
        // register. As a result, the result of an evaluation of an array
        // becomes not the array itself but the address of the array.
        // This is where "array is automatically converted to a pointer to
        // the first element of the array in C" occurs.
        return output;
    }

    let size = ty.borrow().size.unwrap();
    if size == 1 {
        writeln!(&mut output, "  movsbq rax, [rax]").unwrap();
    } else if size == 2 {
        writeln!(&mut output, "  movswq rax, [rax]").unwrap();
    } else if size == 4 {
        writeln!(&mut output, "  movsxd rax, [rax]").unwrap();
    } else {
        writeln!(&mut output, "  mov rax, [rax]").unwrap();
    }
    output
}

pub fn gen_program(program: &mut Program) -> Result<String> {
    let mut output = String::new();
    writeln!(&mut output, ".file 1 \"{}\"", program.ctx.filename).unwrap();
    writeln!(&mut output, ".intel_syntax noprefix").unwrap();
    let globals = program.ctx.scopes.first().unwrap();
    for (_, obj) in globals {
        write!(&mut output, "{}", emit_data(obj, &program.ctx)?).unwrap();
    }
    let funcs = &program.funcs;
    for func in funcs {
        write!(&mut output, "{}", emit_text(func, &mut program.ctx)?).unwrap();
    }
    Ok(output)
}

fn emit_data(obj: &Obj, ctx: &Context) -> Result<String> {
    let mut output = String::new();
    if let ObjKind::Global(name) = &obj.kind {
        if !obj.ty.borrow().is_func() {
            writeln!(&mut output, ".data").unwrap();
            writeln!(&mut output, ".globl {}", name).unwrap();
            writeln!(&mut output, "{}:", name).unwrap();
            if let Some(bytes) = ctx.init_data.get(name) {
                for b in bytes {
                    writeln!(&mut output, "  .byte {}", b).unwrap();
                }
                writeln!(&mut output, "  .byte 0").unwrap();
            } else {
                writeln!(&mut output, "  .zero {}", obj.ty.borrow().size.unwrap()).unwrap();
            }
        }
    }
    Ok(output)
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
    let mut output = String::new();
    writeln!(&mut output, ".globl {}", func.name).unwrap();
    writeln!(&mut output, ".text").unwrap();
    writeln!(&mut output, "{}:", func.name).unwrap();
    // Prologue
    writeln!(&mut output, "  push rbp").unwrap();
    writeln!(&mut output, "  mov rbp, rsp").unwrap();
    writeln!(&mut output, "  sub rsp, {}", func.stack_size).unwrap();
    // Save passed-by-register arguments to the stack
    for (r, obj) in func.params.iter().enumerate() {
        if let ObjKind::Local(offset) = obj.kind {
            write!(
                &mut output,
                "{}",
                store_gp(r, offset, obj.ty.borrow().size.unwrap())
            )
            .unwrap();
        } else {
            unreachable!();
        }
    }
    // Body
    write!(&mut output, "{}", gen_stmt(&func.body, ctx)?).unwrap();
    // Epilogue
    writeln!(&mut output, "  mov rsp, rbp").unwrap();
    writeln!(&mut output, "  pop rbp").unwrap();
    writeln!(&mut output, "  ret").unwrap();
    Ok(output)
}

fn gen_stmt(stmt: &Stmt, ctx: &mut Context) -> Result<String> {
    let mut output = String::new();
    writeln!(&mut output, "  .loc 1 {}", ctx.line_no[stmt.loc] + 1).unwrap();
    match &stmt.kind {
        StmtKind::NullStmt => Ok(output),
        StmtKind::ExprStmt(expr) => {
            write!(&mut output, "{}", gen_expr(expr, ctx)?).unwrap();
            Ok(output)
        }
        StmtKind::ReturnStmt(expr) => {
            write!(&mut output, "{}", gen_expr(&expr, ctx)?).unwrap();
            writeln!(&mut output, "  mov rsp, rbp").unwrap();
            writeln!(&mut output, "  pop rbp").unwrap();
            writeln!(&mut output, "  ret").unwrap();
            Ok(output)
        }
        StmtKind::CompoundStmt(stmt_vec) => {
            for stmt in stmt_vec {
                write!(&mut output, "{}", gen_stmt(stmt, ctx)?).unwrap();
            }
            Ok(output)
        }
        StmtKind::IfStmt { cond, then, els } => {
            write!(&mut output, "{}", gen_expr(&cond, ctx)?).unwrap();
            writeln!(&mut output, "  cmp rax, 0").unwrap();
            writeln!(&mut output, "  je .L.else.{}", ctx.id).unwrap();
            write!(&mut output, "{}", gen_stmt(then, ctx)?).unwrap();
            writeln!(&mut output, "  jmp .L.end.{}", ctx.id).unwrap();
            writeln!(&mut output, ".L.else.{}:", ctx.id).unwrap();
            if let Some(els) = els {
                write!(&mut output, "{}", gen_stmt(els, ctx)?).unwrap();
            }
            writeln!(&mut output, ".L.end.{}:", ctx.id).unwrap();
            ctx.id += 1;
            Ok(output)
        }
        StmtKind::ForStmt {
            init,
            cond,
            inc,
            body,
        } => {
            write!(&mut output, "{}", gen_stmt(init, ctx)?).unwrap();
            writeln!(&mut output, ".L.begin.{}:", ctx.id).unwrap();
            if let Some(cond) = cond {
                write!(&mut output, "{}", gen_expr(cond, ctx)?).unwrap();
                writeln!(&mut output, "  cmp rax, 0").unwrap();
                writeln!(&mut output, "  je .L.end.{}", ctx.id).unwrap();
            }
            write!(&mut output, "{}", gen_stmt(body, ctx)?).unwrap();
            if let Some(inc) = inc {
                write!(&mut output, "{}", gen_expr(inc, ctx)?).unwrap();
            }
            writeln!(&mut output, "  jmp .L.begin.{}", ctx.id).unwrap();
            writeln!(&mut output, ".L.end.{}:", ctx.id).unwrap();
            ctx.id += 1;
            Ok(output)
        }
        StmtKind::WhileStmt { cond, body } => {
            writeln!(&mut output, ".L.begin.{}:", ctx.id).unwrap();
            write!(&mut output, "{}", gen_expr(cond, ctx)?).unwrap();
            writeln!(&mut output, "  cmp rax, 0").unwrap();
            writeln!(&mut output, "  je .L.end.{}", ctx.id).unwrap();
            write!(&mut output, "{}", gen_stmt(body, ctx)?).unwrap();
            writeln!(&mut output, "  jmp .L.begin.{}", ctx.id).unwrap();
            writeln!(&mut output, ".L.end.{}:", ctx.id).unwrap();
            ctx.id += 1;
            Ok(output)
        }
    }
}

// Generate text for a given node.
fn gen_expr(expr: &Expr, ctx: &mut Context) -> Result<String> {
    let mut output = String::new();
    writeln!(&mut output, "  .loc 1 {}", ctx.line_no[expr.loc] + 1).unwrap();
    match &expr.kind {
        ExprKind::StmtExpr(stmt_vec) => {
            for stmt in stmt_vec {
                write!(&mut output, "{}", gen_stmt(stmt, ctx)?).unwrap();
            }
        }
        ExprKind::Assign { lhs, rhs } => {
            write!(&mut output, "{}", gen_addr(&lhs, ctx)?).unwrap();
            write!(&mut output, "{}", push()).unwrap();
            write!(&mut output, "{}", gen_expr(&rhs, ctx)?).unwrap();
            write!(&mut output, "{}", store(&expr.ty)).unwrap();
        }
        ExprKind::Binary {
            op: BinaryOp::COMMA,
            lhs,
            rhs,
        } => {
            write!(&mut output, "{}", gen_expr(&lhs, ctx)?).unwrap();
            write!(&mut output, "{}", gen_expr(&rhs, ctx)?).unwrap();
        }
        ExprKind::Binary { op, lhs, rhs } => {
            write!(&mut output, "{}", gen_expr(&rhs, ctx)?).unwrap();
            write!(&mut output, "{}", push()).unwrap();
            write!(&mut output, "{}", gen_expr(&lhs, ctx)?).unwrap();
            write!(&mut output, "{}", pop("rdi")).unwrap();
            let ax: &'static str;
            let di: &'static str;
            if lhs.ty.borrow().is_long() || lhs.ty.borrow().is_ptr() {
                ax = "rax";
                di = "rdi";
            } else {
                ax = "eax";
                di = "edi";
            }
            match op {
                BinaryOp::ADD => {
                    writeln!(&mut output, "  add {}, {}", ax, di).unwrap();
                }
                BinaryOp::SUB => {
                    writeln!(&mut output, "  sub {}, {}", ax, di).unwrap();
                }
                BinaryOp::MUL => {
                    writeln!(&mut output, "  imul {}, {}", ax, di).unwrap();
                }
                BinaryOp::DIV => {
                    if lhs.ty.borrow().is_long() {
                        writeln!(&mut output, "  cqo").unwrap();
                    } else {
                        writeln!(&mut output, "  cdq").unwrap();
                    }
                    writeln!(&mut output, "  idiv {}", di).unwrap();
                }
                BinaryOp::EQ => {
                    writeln!(&mut output, "  cmp {}, {}", ax, di).unwrap();
                    writeln!(&mut output, "  sete al").unwrap();
                    writeln!(&mut output, "  movzb rax, al").unwrap();
                }
                BinaryOp::NE => {
                    writeln!(&mut output, "  cmp {}, {}", ax, di).unwrap();
                    writeln!(&mut output, "  setne al").unwrap();
                    writeln!(&mut output, "  movzb rax, al").unwrap();
                }
                BinaryOp::LT => {
                    writeln!(&mut output, "  cmp {}, {}", ax, di).unwrap();
                    writeln!(&mut output, "  setl al").unwrap();
                    writeln!(&mut output, "  movzb rax, al").unwrap();
                }
                BinaryOp::LE => {
                    writeln!(&mut output, "  cmp {}, {}", ax, di).unwrap();
                    writeln!(&mut output, "  setle al").unwrap();
                    writeln!(&mut output, "  movzb rax, al").unwrap();
                }
                BinaryOp::COMMA => {}
            };
        }
        ExprKind::Unary { op, expr: operand } => {
            match op {
                UnaryOp::NEG => {
                    write!(&mut output, "{}", gen_expr(&operand, ctx)?).unwrap();
                    writeln!(&mut output, "  neg rax").unwrap();
                }
                UnaryOp::DEREF => {
                    write!(&mut output, "{}", gen_expr(&operand, ctx)?).unwrap();
                    write!(&mut output, "{}", load(&expr.ty)).unwrap();
                }
                UnaryOp::ADDR => {
                    write!(&mut output, "{}", gen_addr(&operand, ctx)?).unwrap();
                }
            };
        }
        ExprKind::Member { expr: _, offset: _ } => {
            write!(&mut output, "{}", gen_addr(expr, ctx)?).unwrap();
            write!(&mut output, "{}", load(&expr.ty)).unwrap();
        }
        ExprKind::Var(_) => {
            write!(&mut output, "{}", gen_addr(expr, ctx)?).unwrap();
            write!(&mut output, "{}", load(&expr.ty)).unwrap();
        }
        ExprKind::Num(val) => {
            writeln!(&mut output, "  mov rax, {}", val).unwrap();
        }
        ExprKind::FunCall { name, args } => {
            let argreg = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
            let mut nargs = 0;
            for arg in args {
                write!(&mut output, "{}", gen_expr(arg, ctx)?).unwrap();
                write!(&mut output, "{}", push()).unwrap();
                nargs += 1;
            }
            for i in (0..nargs).rev() {
                write!(&mut output, "{}", pop(argreg[i])).unwrap();
            }
            // todo: RSP must be align to 16
            writeln!(&mut output, "  call {}", name).unwrap();
        }
    };
    Ok(output)
}
