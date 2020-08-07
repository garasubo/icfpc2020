use crate::symbol::Symbol;
use failure::_core::cell::RefCell;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedSymbol {
    Number(i128),
    Nil,
    Cons,
    Car,
    Cdr,
    BComb,
    CComb,
    SComb,
    IComb,
    True,
    False,
    Variable(i128),
    Neg,
    Sum,
    Prod,
    Div,
    Less,
    IsNil,
    BigEq,
}

impl TypedSymbol {
    pub fn typing(sym: &Symbol) -> Option<Self> {
        use TypedSymbol::*;

        match sym {
            Symbol::Number(i) => Some(Number(*i)),
            Symbol::Nil => Some(Nil),
            Symbol::Cons => Some(Cons),
            Symbol::Car => Some(Car),
            Symbol::Cdr => Some(Cdr),
            Symbol::BComb => Some(BComb),
            Symbol::CComb => Some(CComb),
            Symbol::SComb => Some(SComb),
            Symbol::IComb => Some(IComb),
            Symbol::True => Some(True),
            Symbol::False => Some(False),
            Symbol::Variable(i) => Some(Variable(*i)),
            Symbol::Sum => Some(Sum),
            Symbol::Prod => Some(Prod),

            Symbol::Neg => Some(Neg),
            Symbol::Div => Some(Div),
            Symbol::Less => Some(Less),
            Symbol::IsNil => Some(IsNil),
            Symbol::BigEq => Some(BigEq),
            _ => todo!("todo: {:?}", sym),
        }
    }
}

pub type ExprNode<'a> = &'a TypedExpr<'a>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedExpr<'a> {
    Apply(ExprNode<'a>, ExprNode<'a>),
    List(ExprNode<'a>, ExprNode<'a>),
    LazyNode(RefCell<ExprNode<'a>>),
    Val(TypedSymbol),
}

impl<'a> TypedExpr<'a> {
    pub fn get_number(&self) -> Option<i128> {
        match self {
            TypedExpr::Val(TypedSymbol::Number(x)) => Some(*x),
            _ => {
                eprintln!("not number: {:?}", self);
                None
            },
        }
    }
}

pub mod raku {
    use super::TypedExpr::*;
    use super::TypedSymbol::*;
    use super::*;
    pub const NIL: TypedExpr<'static> = Val(Nil);
    pub const CONS: TypedExpr<'static> = Val(Cons);
    pub const CAR: TypedExpr<'static> = Val(Car);
    pub const CDR: TypedExpr<'static> = Val(Cdr);
    pub const BCOMB: TypedExpr<'static> = Val(BComb);
    pub const CCOMB: TypedExpr<'static> = Val(CComb);
    pub const ICOMB: TypedExpr<'static> = Val(IComb);
    pub const SUM: TypedExpr<'static> = Val(Sum);
    pub const NEG: TypedExpr<'static> = Val(Neg);
    pub const DIV: TypedExpr<'static> = Val(Div);
    pub const LESS: TypedExpr<'static> = Val(Less);
    pub const EQ: TypedExpr<'static> = Val(BigEq);
    pub const T: TypedExpr<'static> = Val(True);
    pub const F: TypedExpr<'static> = Val(False);
}
