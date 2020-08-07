use std::collections::{HashMap, HashSet};

use crate::expr::Expr;
use crate::typing::*;
use typed_arena::Arena;
use std::time::Instant;
use std::cell::Cell;
use crate::typing::TypedSymbol::Cons;
use std::ops::Deref;
use failure::_core::cell::RefCell;
use crate::typing::TypedExpr::LazyNode;

#[derive(Debug)]
pub enum EvalError<'a> {
    NumberIsExpected(ExprNode<'a>),
    ListIsExpected(ExprNode<'a>),
    UndefinedVariable(i128),
    Todo,
}

pub struct Evaluator<'a> {
    exprs: Arena<TypedExpr<'a>>,
}

impl<'a> Evaluator<'a> {
    pub fn new() -> Self {
        Evaluator {
            exprs: Arena::new(),
        }
    }

    pub fn get_app(&'a self, expr1: ExprNode<'a>, expr2: ExprNode<'a>) -> ExprNode<'a> {
        self.exprs.alloc(TypedExpr::Apply(expr1, expr2))
    }

    pub fn get_val(&'a self, symbol: TypedSymbol) -> ExprNode<'a> {
        self.exprs.alloc(TypedExpr::Val(symbol))
    }

    pub fn get_number(&'a self, v: i128) -> ExprNode<'a> {
        self.exprs.alloc(TypedExpr::Val(TypedSymbol::Number(v)))
    }

    pub fn get_lazy(&'a self, expr: ExprNode<'a>) -> ExprNode<'a> {
        match expr {
            LazyNode(_) | TypedExpr::Val(_) => expr,
            _ => self.exprs.alloc(TypedExpr::LazyNode(RefCell::new(expr)))
        }
    }

    pub fn peel(
        &'a self,
        expr: ExprNode<'a>,
        vars: &HashMap<i128, ExprNode<'a>>,
    ) -> Result<ExprNode, EvalError> {
        use TypedExpr::*;
        use TypedSymbol::*;
        match expr {
            List(e1, e2) => {
                let e1 = self.eval(e1, vars)?;
                let e1 = self.peel(e1, vars)?;
                let e2 = self.eval(e2, vars)?;
                let e2 = self.peel(e2, vars)?;
                Ok(self.get_list(e1, e2))
            }
            Apply(Apply(Val(Cons), x0), x) => {
                let x0 = self.eval(x0, vars)?;
                let x0 = self.peel(x0, vars)?;
                let x1 = self.eval(x, vars)?;
                let x1 = self.peel(x1, vars)?;
                Ok(self.get_list(x0, x1))
            }
            LazyNode(refcell) => {
                let expr = self.peel(refcell.borrow().deref(), vars)?;
                refcell.replace(expr);
                Ok(expr)
            }
            _ => Ok(expr),
        }
    }

    pub fn get_cons(&'a self, e1: ExprNode<'a>, e2: ExprNode<'a>) -> ExprNode<'a> {
        let cons = self.get_val(Cons);
        let e3 = self.exprs.alloc(TypedExpr::Apply(cons, e1));
        self.exprs.alloc(TypedExpr::Apply(e3, e2))
    }

    pub fn get_list(&'a self, e1: ExprNode<'a>, e2: ExprNode<'a>) -> ExprNode<'a> {
        self.exprs.alloc(TypedExpr::List(e1, e2))
    }

    pub fn eval2(
        &'a self,
        expr: ExprNode<'a>,
        vars: &HashMap<i128, ExprNode<'a>>,
    ) -> Result<ExprNode, EvalError> {
        let start = Instant::now();
        let expr = self.optimize(expr, vars, &mut HashSet::new())?;
        let vars: HashMap<i128, ExprNode<'a>> = vars.iter()
            .map(|(i, expr)| {
                (*i, self.get_lazy(expr))
            })
            .collect();
        eprintln!("optimize expr: {} ms", start.elapsed().as_millis());
        let expr = self.eval(expr, &vars)?;
        eprintln!("eval expr: {} ms", start.elapsed().as_millis());
        // println!("{}", env.keys().len());
        let result = self.peel(expr, &vars);
        eprintln!("peel expr: {} ms", start.elapsed().as_millis());
        result
    }

    pub fn optimize(
        &'a self,
        expr: ExprNode<'a>,
        vars: &HashMap<i128, ExprNode<'a>>,
        used: &mut HashSet<i128>,
    ) -> Result<ExprNode, EvalError> {
        use TypedExpr::*;
        use TypedSymbol::*;

        match expr {
            Val(Variable(i)) => {
                if let Some(body) = vars.get(i) {
                    Ok(body)
                } else if used.contains(i) {
                    Ok(expr)
                } else {
                    used.insert(*i);
                    self.optimize(expr, vars, used)
                }
            },
            Val(_) => Ok(expr),
            Apply(f, x0) => {
                let func = self.optimize(f, vars, used)?;
                let x = self.optimize(x0, vars, used)?;
                match func {
                    Val(IComb) => Ok(x),
                    Val(Neg) => {
                        if let Val(Number(i)) = x {
                            Ok(self.get_number(-*i))
                        } else {
                            Ok(expr)
                        }
                    }
                    Val(Nil) => {
                        Ok(self.get_val(True))
                    }
                    Val(_) => {
                        Ok(expr)
                    }
                    Apply(Val(Sum), Val(Number(i))) => {
                        if let Val(Number(j)) = x {
                            Ok(self.get_number(i+j))
                        } else {
                            Ok(expr)
                        }
                    }
                    Apply(Val(Div), Val(Number(i))) => {
                        if let Val(Number(j)) = x {
                            Ok(self.get_number(i/j))
                        } else {
                            Ok(expr)
                        }
                    }
                    Apply(Val(Prod), Val(Number(i))) => {
                        if let Val(Number(j)) = x {
                            Ok(self.get_number(i*j))
                        } else {
                            Ok(expr)
                        }
                    }
                    Apply(Val(Less), Val(Number(i))) => {
                        if let Val(Number(j)) = x {
                            if i < j {
                                Ok(self.get_val(True))
                            } else {
                                Ok(self.get_val(False))
                            }
                        } else {
                            Ok(expr)
                        }
                    }
                    Apply(Val(BigEq), Val(Number(i))) => {
                        if let Val(Number(j)) = x {
                            if i == j {
                                Ok(self.get_val(True))
                            } else {
                                Ok(self.get_val(False))
                            }
                        } else {
                            Ok(expr)
                        }
                    }
                    _ => Ok(expr)
                }
            }
            _ => { Ok(expr) }
        }
    }

    fn eval(
        &'a self,
        expr: ExprNode<'a>,
        vars: &HashMap<i128, ExprNode<'a>>,
    ) -> Result<ExprNode, EvalError> {
        use EvalError::*;
        use TypedExpr::*;
        use TypedSymbol::*;

        // println!("evaluating {:?}", expr);

        //if let Some(evaluated) = env.get(&expr) {
        //    return Ok(evaluated);
        //}

        match expr {
            Val(Variable(i)) => {
                let body = vars.get(&i).ok_or(UndefinedVariable(*i))?;
                let body = self.eval(body, vars)?;
                // env.insert(expr.clone(), body);
                Ok(body)
            }
            Val(_) => Ok(expr),
            Apply(f, x) => {
                let func = self.eval(f, vars)?;
                match func {
                    // Car
                    Val(Car) => {
                        match x {
                            List(e1, e2) => {
                                self.eval(e1, vars)
                            }
                            _ => {
                                // ap car x   =   ap x t
                                let v = self.get_app(*x, self.get_val(True));
                                let res = self.eval(v, vars)?;
                                // env.insert(expr.clone(), res);
                                Ok(res)
                            }
                        }
                    }
                    // Cdr
                    Val(Cdr) => {
                        match x {
                            List(e1, e2) => {
                                self.eval(e2, vars)
                            }
                            _ => {
                                // ap cdr x2   =   ap x2 f
                                let v = self.get_app(*x, self.get_val(False));
                                let res = self.eval(v, vars)?;
                                // env.insert(expr.clone(), res);
                                Ok(res)
                            }
                        }
                    }
                    // I-Combinator
                    Val(IComb) => {
                        // ap i x0   =   x0
                        let res = self.eval(x, vars)?;
                        Ok(res)
                    }
                    Val(Neg) => {
                        let x = self.eval(*x, vars)?;
                        let x = x.get_number().unwrap();
                        Ok(self.get_val(Number(-x)))
                    }
                    Val(Nil) => Ok(self.get_val(TypedSymbol::True)),
                    Val(IsNil) => {
                        let e = self.eval(*x, vars)?;
                        match e {
                            Val(Nil) => Ok(self.get_val(True)),
                            Val(Cons) => Ok(self.get_val(False)),
                            List(_, _) => Ok(self.get_val(False)),
                            _ => {
                                Err(ListIsExpected(e))
                            },
                        }
                    }
                    // 2 or 3 pair operators
                    Val(_) => {
                        //eprintln!("Wait other props {:?}", func);
                        Ok(self.get_app(func, x))
                    }
                    Apply(Val(Cons), x0) => {
                        Ok(self.get_list(x0, x))
                    }
                    Apply(Val(Sum), x0) => {
                        let n0 = self.eval(x0, vars)?.get_number().unwrap();
                        let n1 = self.eval(x, vars)?.get_number().unwrap();
                        Ok(self.get_number(n0 + n1))
                    }
                    Apply(Val(Prod), x0) => {
                        let n0 = self.eval(x0, vars)?.get_number().unwrap();
                        let n1 = self.eval(x, vars)?.get_number().unwrap();
                        Ok(self.get_number(n0 * n1))
                    }
                    Apply(Val(Div), x0) => {
                        let n0 = self.eval(x0, vars)?.get_number().unwrap();
                        let n1 = self.eval(x, vars)?.get_number().unwrap();
                        Ok(self.get_number(n0 / n1))
                    }
                    Apply(Val(Less), x0) => {
                        let n0 = self.eval(x0, vars)?.get_number().unwrap();
                        let n1 = self.eval(x, vars)?.get_number().unwrap();
                        if n0 < n1 {
                            Ok(self.get_val(True))
                        } else {
                            Ok(self.get_val(False))
                        }
                    }
                    Apply(Val(BigEq), x0) => {
                        let n0 = self.eval(x0, vars)?.get_number().unwrap();
                        let n1 = self.eval(x, vars)?.get_number().unwrap();
                        if n0 == n1 {
                            Ok(self.get_val(True))
                        } else {
                            Ok(self.get_val(False))
                        }
                    }
                    Apply(Val(True), x0) => {
                        self.eval(x0, vars)
                    }
                    Apply(Val(False), _) => {
                        self.eval(x, vars)
                    }
                    Apply(Apply(Val(BComb), x0), x1) => {
                        let e = self.get_app(
                            x0,
                            self.get_app(
                                x1,
                                x));
                        self.eval(e, vars)
                    }
                    Apply(Apply(Val(CComb), x0), x1) => {
                        let e = self.get_app(
                            self.get_app(
                                x0,
                                x),
                            x1);
                        self.eval(e, vars)
                    }
                    Apply(Apply(Val(SComb), x0), x1) => {
                        let x2 = self.get_lazy(x);
                        let e1 = self.get_app(x0, x2);
                        let e2 = self.get_app(x1, x2);
                        let e = self.get_app(e1, e2);
                        self.eval(e, vars)
                    }
                    Apply(Apply(Val(Cons), x0), x1) => {
                        let e = self.get_app(self.get_app(x, x0), x1);
                        self.eval(e, vars)
                    }
                    List(e1, e2) => {
                        self.eval(self.get_app(self.get_app(x, e1), e2), vars)
                    }
                    _ => {
                        //eprintln!("Applying f={:?} to x={:?} (original: {:?})", func, x, f);
                        Ok(self.get_app(func, x))
                    }
                }
            }
            LazyNode(expr) => {
                let evaluated = self.eval(expr.borrow().deref(), vars)?;
                let original = expr.replace(evaluated);
                // eprintln!("Lazy eval: {:?} to {:?}", original, evaluated);
                Ok(evaluated)
            }
            List(_, _) => Ok(expr),
            _ => {
                eprintln!("unexpected pattern: {:?}", expr);
                Err(Todo)
            }
        }
    }

    pub fn typing(&'a self, expr: &Expr) -> Option<ExprNode<'a>> {
        match expr {
            Expr::Val(sym) => TypedSymbol::typing(sym).map(|s| self.get_val(s)),
            Expr::Apply(e1, e2) => match (self.typing(e1), self.typing(e2)) {
                (Some(t1), Some(t2)) => Some(self.get_app(t1, t2)),
                _ => None,
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::typing::TypedSymbol::*;

    fn empty_env<'a>() -> HashMap<i128, ExprNode<'a>> {
        HashMap::new()
    }

    #[test]
    fn test_div_numerator_minus() {
        let eval = Evaluator::new();
        // ap ap div -5 3   =   -1
        let div = eval.get_val(Div);
        let exp1 = eval.get_app(div, eval.get_number(-5));
        let exp2 = eval.get_app(exp1, eval.get_number(3));
        let e = eval.eval2(exp2, &empty_env()).unwrap();
        assert_eq!(e, eval.get_number(-1))
    }

    #[test]
    fn test_comb_b() {
        // B neg neg x = x
        for x in -3..4 {
            let mut eval = Evaluator::new();
            let expr = eval.get_app(
                eval.get_app(eval.get_app(eval.get_val(BComb), eval.get_val(Neg)), eval.get_val(Neg)),
                eval.get_number(x),
            );
            assert_eq!(eval.get_number(x), eval.eval2(&expr, &empty_env()).unwrap());
        }
    }

    #[test]
    fn test_comb_i() {
        // I x = x
        {
            let eval = Evaluator::new();
            let expr = eval.get_app(eval.get_val(IComb), eval.get_val(Neg));
            let mut env = HashMap::new();
            assert_eq!(eval.get_val(Neg), eval.eval2(&expr, &mut env).unwrap());
        }
        {
            let mut eval = Evaluator::new();
            let expr = eval.get_app(eval.get_val(IComb), eval.get_val(BComb));
            let mut env = HashMap::new();
            assert_eq!(eval.get_val(BComb), eval.eval2(&expr, &mut env).unwrap());
        }
    }

    #[test]
    fn test_comb_s() {
        let eval = Evaluator::new();
        // ap ap ap s add inc 1 = 3
        let s = eval.get_val(SComb);
        let add = eval.get_val(Sum);
        let n1 = eval.get_number(1);
        let inc = eval.get_app(add, n1);
        let e1 = eval.get_app(s, add);
        let e2 = eval.get_app(e1, inc);
        let e3 = eval.get_app(e2, n1);
        assert_eq!(eval.get_number(3), eval.eval2(e3, &empty_env()).unwrap());
    }

    #[test]
    fn test_comb_c() {
        let eval = Evaluator::new();
        // ap ap ap c div 1 2 = 2
        let c = eval.get_val(CComb);
        let add = eval.get_val(Div);
        let n1 = eval.get_number(1);
        let n2 = eval.get_number(2);
        let e1 = eval.get_app(c, add);
        let e2 = eval.get_app(e1, n1);
        let e3 = eval.get_app(e2, n2);
        assert_eq!(eval.get_number(2), eval.eval2(e3, &empty_env()).unwrap());
    }

    #[test]
    fn test_list() {
        let eval = Evaluator::new();
        // (x0, x1) = ap ap cons x0 ap ap cons x1 nil
        let cons = eval.get_val(Cons);
        let x0 = eval.get_number(0);
        let x1 = eval.get_number(0);
        let e1 = eval.get_app(cons, x0);
        let e2 = eval.get_app(cons, x1);
        let e3 = eval.get_app(e2, eval.get_val(Nil));
        let e4 = eval.get_app(e1, e3);
        assert_eq!(eval.get_list(x0, eval.get_list(x1, eval.get_val(Nil))), eval.eval2(e4, &empty_env()).unwrap());
    }

    #[test]
    fn test_car() {
        let eval = Evaluator::new();
        // x0 = ap car ap ap cons x0 ap ap cons x1 nil
        let cons = eval.get_val(Cons);
        let car = eval.get_val(Car);
        let x0 = eval.get_number(0);
        let x1 = eval.get_number(0);
        let e1 = eval.get_app(cons, x0);
        let e2 = eval.get_app(cons, x1);
        let e3 = eval.get_app(e2, eval.get_val(Nil));
        let e4 = eval.get_app(e1, e3);
        let e5 = eval.get_app(car, e4);
        assert_eq!(x0, eval.eval2(e5, &empty_env()).unwrap());
    }

    #[test]
    fn test_cdr() {
        let eval = Evaluator::new();
        // x0 = ap car ap ap cons x0 ap ap cons x1 nil
        let cons = eval.get_val(Cons);
        let cdr = eval.get_val(Car);
        let x0 = eval.get_number(0);
        let x1 = eval.get_number(0);
        let e1 = eval.get_app(cons, x0);
        let e2 = eval.get_app(cons, x1);
        let e3 = eval.get_app(e2, eval.get_val(Nil));
        let e4 = eval.get_app(e1, e3);
        let e5 = eval.get_app(cdr, e4);
        assert_eq!(x1, eval.eval2(e5, &empty_env()).unwrap());
    }

    #[test]
    fn var_apply() {
        let eval = Evaluator::new();
        let mut env = HashMap::new();
        let add = eval.get_val(Sum);
        env.insert(1, add);
        let n5 = eval.get_number(5);
        let n7 = eval.get_number(7);
        env.insert(2, n5);
        env.insert(3, n7);
        let var1 = eval.get_val(Variable(1));
        let var2 = eval.get_val(Variable(2));
        let var3 = eval.get_val(Variable(3));
        let e = eval.get_app(eval.get_app(var1, var2), var3);
        assert_eq!(eval.get_number(12), eval.eval2(e, &env).unwrap());
    }

    #[test]
    fn complex_eval() {
        use crate::symbol::Symbol::*;
        let eval = Evaluator::new();
        let symbols = vec![
            App, App, IComb, Nil,
            App, App, App, SComb, App, App, BComb, CComb, App, App, BComb, BComb, BComb,
            App, BigEq, Number(0), App, App, BComb, App, CComb, Number(2), App, Sum, Number(-1), Number(1)
        ];
        let expr = crate::expr::parse(&symbols);
        let expr = eval.typing(&expr).unwrap();
        assert_eq!(eval.get_val(TypedSymbol::True), eval.eval(expr, &empty_env()).unwrap());
    }

    #[test]
    fn lazy_eval_icomb() {
        let eval = Evaluator::new();
        let var1 = eval.get_val(Variable(1));
        let icomb = eval.get_val(IComb);
        let add = eval.get_val(Sum);
        let n1 = eval.get_number(1);
        let inc = eval.get_app(add, n1);

        let lexpr = eval.get_lazy(eval.get_app(icomb, inc));
        let mut env = HashMap::new();
        env.insert(1, inc);
        let expr = eval.get_app(lexpr, n1);
        assert_eq!(eval.get_number(2), eval.eval(expr, &env).unwrap());
    }
}
