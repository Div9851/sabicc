use crate::parse::{Node, NodeKind};

fn push() {
    println!("  push rax");
}

fn pop(reg: &str) {
    println!("  pop {}", reg);
}

pub fn gen_expr(node: &Node) {
    if node.kind == NodeKind::NUM {
        println!("  mov rax, {}", node.val.unwrap());
        return;
    }
    if node.kind == NodeKind::NEG {
        gen_expr(node.lhs.as_ref().unwrap());
        println!("  neg rax");
        return;
    }
    gen_expr(node.rhs.as_ref().unwrap());
    push();
    gen_expr(node.lhs.as_ref().unwrap());
    pop("rdi");
    match node.kind {
        NodeKind::ADD => {
            println!("  add rax, rdi");
        }
        NodeKind::SUB => {
            println!("  sub rax, rdi");
        }
        NodeKind::MUL => {
            println!("  imul rax, rdi");
        }
        NodeKind::DIV => {
            println!("  cqo");
            println!("  idiv rdi");
        }
        NodeKind::EQ => {
            println!("  cmp rax, rdi");
            println!("  sete al");
            println!("  movzb rax, al");
        }
        NodeKind::NE => {
            println!("  cmp rax, rdi");
            println!("  setne al");
            println!("  movzb rax, al");
        }
        NodeKind::LT => {
            println!("  cmp rax, rdi");
            println!("  setl al");
            println!("  movzb rax, al");
        }
        NodeKind::LE => {
            println!("  cmp rax, rdi");
            println!("  setle al");
            println!("  movzb rax, al");
        }
        _ => {
            panic!("NodeKind::{:?} is missing", node.kind);
        }
    };
}
