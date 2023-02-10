use crate::{
    error::Error,
    parse::{BinaryOperator, Expr, Func, Stmt, UnaryOperator},
};

fn push() {
    println!("  push rax");
}

fn pop(reg: &str) {
    println!("  pop {}", reg);
}

pub fn gen_func(func: &Func) -> Result<(), Error> {
    // Prologue
    println!("  push rbp");
    println!("  mov rbp, rsp");
    println!("  sub rsp, {}", func.stack_size);
    // Body
    gen_stmt(&func.body)?;
    // Epilogue
    println!("  mov rsp, rbp");
    println!("  pop rbp");
    println!("  ret");
    Ok(())
}

fn gen_stmt(stmt: &Stmt) -> Result<(), Error> {
    match stmt {
        Stmt::NullStmt => Ok(()),
        Stmt::ExprStmt(expr) => {
            gen_expr(expr)?;
            Ok(())
        }
        Stmt::ReturnStmt(expr) => {
            gen_expr(expr)?;
            println!("  mov rsp, rbp");
            println!("  pop rbp");
            println!("  ret");
            Ok(())
        }
        Stmt::Block(block) => {
            for stmt in block {
                gen_stmt(stmt)?;
            }
            Ok(())
        }
    }
}

fn gen_expr(expr: &Expr) -> Result<(), Error> {
    match expr {
        Expr::Assign { lhs, rhs } => {
            gen_addr(lhs)?;
            push();
            gen_expr(rhs)?;
            pop("rdi");
            println!("  mov [rdi], rax");
        }
        Expr::Binary { op, lhs, rhs } => {
            gen_expr(rhs)?;
            push();
            gen_expr(lhs)?;
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
        Expr::Unary { op, expr } => {
            gen_expr(expr)?;
            match op {
                UnaryOperator::NEG => {
                    println!("  neg rax");
                }
            };
        }
        Expr::Var(_) => {
            gen_addr(expr)?;
            println!("  mov rax, [rax]");
        }
        Expr::Num(val) => {
            println!("  mov rax, {}", val);
        }
    };
    Ok(())
}

fn gen_addr(expr: &Expr) -> Result<(), Error> {
    if let Expr::Var(obj) = expr {
        println!("  lea rax, [rbp-{}]", obj.offset);
        return Ok(());
    }
    Err(Error {
        loc: 0,
        msg: "not an lvalue".to_owned(),
    })
}
