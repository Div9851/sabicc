use crate::parse::{BinaryOperator, Expr, UnaryOperator};

fn push() {
    println!("  push rax");
}

fn pop(reg: &str) {
    println!("  pop {}", reg);
}

pub fn gen_expr(node: &Expr) {
    match node {
        Expr::Binary { op, lhs, rhs } => {
            gen_expr(rhs);
            push();
            gen_expr(lhs);
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
            }
        }
        Expr::Unary { op, expr } => {
            gen_expr(expr);
            match op {
                UnaryOperator::NEG => {
                    println!("  neg rax");
                }
            }
        }
        Expr::Num(val) => {
            println!("  mov rax, {}", val);
        }
    }
}
