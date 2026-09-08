//! Iterative AST depth measurement. Parser recursion alone cannot bound a
//! left-associated operator/postfix chain built by a loop. Check each extension
//! before the tree grows large enough to overflow later visitors or Drop.
use crate::ast::{Block, Expr, FStringPart, Stmt, SupervisionExpr};

enum Node<'a> {
    Expr(&'a Expr),
    Block(&'a Block),
    Stmt(&'a Stmt),
}

pub(super) fn expression_too_deep(expr: &Expr, max: usize) -> bool {
    too_deep(Node::Expr(expr), max)
}

pub(super) fn block_too_deep(block: &Block, max: usize) -> bool {
    too_deep(Node::Block(block), max)
}

fn too_deep(root: Node<'_>, max: usize) -> bool {
    let mut pending = vec![(root, 1)];
    while let Some((node, depth)) = pending.pop() {
        if depth > max {
            return true;
        }
        let mut push = |node| pending.push((node, depth + 1));
        match node {
            Node::Block(block) => {
                for statement in &block.statements {
                    push(Node::Stmt(statement));
                }
            }
            Node::Stmt(statement) => match statement {
                Stmt::Let(s) => push(Node::Expr(&s.value)),
                Stmt::LetTuple(s) => push(Node::Expr(&s.value)),
                Stmt::Assign(s) => {
                    push(Node::Expr(&s.target));
                    push(Node::Expr(&s.value));
                }
                Stmt::Expr(s) => push(Node::Expr(&s.expr)),
                Stmt::Return(s) => {
                    if let Some(e) = &s.value {
                        push(Node::Expr(e));
                    }
                }
                Stmt::If(s) => {
                    push(Node::Expr(&s.condition));
                    push(Node::Block(&s.then_branch));
                    push(Node::Block(&s.else_branch));
                }
                Stmt::Match(s) => {
                    push(Node::Expr(&s.scrutinee));
                    for arm in &s.arms {
                        if let Some(guard) = &arm.guard {
                            push(Node::Expr(guard));
                        }
                        push(Node::Block(&arm.body));
                    }
                }
                Stmt::While(s) => {
                    push(Node::Expr(&s.condition));
                    push(Node::Block(&s.body));
                }
                Stmt::ForIn(s) => {
                    push(Node::Expr(&s.iterable));
                    push(Node::Block(&s.body));
                }
                Stmt::ForRange(s) => {
                    push(Node::Expr(&s.start));
                    push(Node::Expr(&s.end));
                    push(Node::Block(&s.body));
                }
                Stmt::Break(_) | Stmt::Continue(_) => {}
            },
            Node::Expr(expr) => match expr {
                Expr::Literal(_)
                | Expr::Path(_)
                | Expr::CapRestrict(_)
                | Expr::CapRestrictDeadline(_) => {}
                Expr::Binary(e) => {
                    push(Node::Expr(&e.lhs));
                    push(Node::Expr(&e.rhs));
                }
                Expr::Call(e) => {
                    for a in &e.args {
                        push(Node::Expr(a));
                    }
                }
                Expr::MethodCall(e) => {
                    push(Node::Expr(&e.receiver));
                    for a in &e.args {
                        push(Node::Expr(a));
                    }
                }
                Expr::ResultCtor(e) => push(Node::Expr(&e.value)),
                Expr::Try(e) => push(Node::Expr(&e.value)),
                Expr::Send(e) => push(Node::Expr(&e.message)),
                Expr::Ask(e) => {
                    push(Node::Expr(&e.message));
                    push(Node::Expr(&e.timeout));
                }
                Expr::Spawn(e) => {
                    for a in &e.args {
                        push(Node::Expr(a));
                    }
                    if let Some(SupervisionExpr::Restart { max_restarts }) = &e.supervision {
                        push(Node::Expr(max_restarts));
                    }
                }
                Expr::EnumConstruct(e) => {
                    for f in &e.fields {
                        push(Node::Expr(f));
                    }
                }
                Expr::RecordConstruct(e) => {
                    for (_, f) in &e.fields {
                        push(Node::Expr(f));
                    }
                }
                Expr::FieldAccess(e) => push(Node::Expr(&e.object)),
                Expr::CapSplit(e) => push(Node::Expr(&e.amount)),
                Expr::CapDraw(e) => push(Node::Expr(&e.amount)),
                Expr::Mint(e) => push(Node::Expr(&e.target)),
                Expr::ArrayLit(e) => {
                    for a in &e.elements {
                        push(Node::Expr(a));
                    }
                }
                Expr::Tuple(e) => {
                    for a in &e.elements {
                        push(Node::Expr(a));
                    }
                }
                Expr::Index(e) => {
                    push(Node::Expr(&e.array));
                    push(Node::Expr(&e.index));
                }
                Expr::Slice(e) => {
                    push(Node::Expr(&e.array));
                    if let Some(a) = &e.start {
                        push(Node::Expr(a));
                    }
                    if let Some(a) = &e.end {
                        push(Node::Expr(a));
                    }
                }
                Expr::Closure(e) => push(Node::Block(&e.body)),
                Expr::Borrow(e) => push(Node::Expr(&e.inner)),
                Expr::Grant(e) => {
                    push(Node::Expr(&e.cap));
                    push(Node::Expr(&e.body));
                }
                Expr::Handle(e) => push(Node::Block(&e.body)),
                Expr::Perform(e) => {
                    for a in &e.args {
                        push(Node::Expr(a));
                    }
                }
                Expr::ClauseHandle(e) => {
                    push(Node::Expr(&e.scrutinee));
                    for c in &e.clauses {
                        push(Node::Block(&c.body));
                    }
                }
                Expr::Resume(e) => push(Node::Expr(&e.value)),
                Expr::Declassify(e) => {
                    push(Node::Expr(&e.value));
                    push(Node::Expr(&e.cap));
                }
                Expr::DeclassifyCt(e) => {
                    push(Node::Expr(&e.value));
                    push(Node::Expr(&e.cap));
                }
                Expr::Region(e) => {
                    push(Node::Expr(&e.limit));
                    push(Node::Block(&e.body));
                }
                Expr::FString(e) => {
                    for p in &e.parts {
                        if let FStringPart::Hole(a) = p {
                            push(Node::Expr(a));
                        }
                    }
                }
            },
        }
    }
    false
}
