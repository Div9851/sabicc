use crate::{
    error::Error,
    parse::{BinaryOperator, Expr, ExprKind, Func, Stmt, StmtKind, Type, TypeKind, UnaryOperator},
};

static ARGREG: [&'static str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];

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

// Compute the absolute address to a given node.
// It's an error if a given node does not reside in memory.
fn gen_addr(expr: &Expr) -> Result<(), Error> {
    if let ExprKind::Var(obj) = &expr.kind {
        println!("  lea rax, [rbp-{}]", obj.offset);
        return Ok(());
    }
    if let ExprKind::Unary {
        op: UnaryOperator::DEREF,
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
    println!("  mov rax, [rax]");
}

pub fn gen_func(func: &Func, ctx: &mut CodegenContext) -> Result<(), Error> {
    println!(".globl {}", func.name);
    println!("{}:", func.name);
    // Prologue
    println!("  push rbp");
    println!("  mov rbp, rsp");
    println!("  sub rsp, {}", align_to(func.stack_size, 16));
    let mut nargs = 0;
    for obj in &func.params {
        println!("  lea rax, [rbp-{}]", obj.offset);
        println!("  mov [rax], {}", ARGREG[nargs]);
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
            pop("rdi");
            println!("  mov [rdi], rax");
        }
        ExprKind::Binary { op, lhs, rhs } => {
            gen_expr(&rhs)?;
            push();
            gen_expr(&lhs)?;
            pop("rdi");
            match op {
                BinaryOperator::ADD => {
                    println!("  add rax, rdi");
                }
                BinaryOperator::SUB => {
                    println!("  sub rax, rdi");
                }
                BinaryOperator::MUL => {
                    println!("  imul rax, rdi");
                }
                BinaryOperator::DIV => {
                    println!("  cqo");
                    println!("  idiv rdi");
                }
                BinaryOperator::EQ => {
                    println!("  cmp rax, rdi");
                    println!("  sete al");
                    println!("  movzb rax, al");
                }
                BinaryOperator::NE => {
                    println!("  cmp rax, rdi");
                    println!("  setne al");
                    println!("  movzb rax, al");
                }
                BinaryOperator::LT => {
                    println!("  cmp rax, rdi");
                    println!("  setl al");
                    println!("  movzb rax, al");
                }
                BinaryOperator::LE => {
                    println!("  cmp rax, rdi");
                    println!("  setle al");
                    println!("  movzb rax, al");
                }
            };
        }
        ExprKind::Unary { op, expr } => {
            match op {
                UnaryOperator::NEG => {
                    gen_expr(&expr)?;
                    println!("  neg rax");
                }
                UnaryOperator::DEREF => {
                    gen_expr(&expr)?;
                    println!("  mov rax, [rax]");
                }
                UnaryOperator::ADDR => {
                    gen_addr(&expr)?;
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
