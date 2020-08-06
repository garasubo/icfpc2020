use std::collections::{HashMap, HashSet};

use crate::eval::static_expr::*;
use crate::expr::Expr;
use crate::typing::*;
use typed_arena::Arena;
use std::time::Instant;

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

pub mod static_expr {
    use crate::typing::TypedExpr;
    use crate::typing::TypedExpr::*;
    use crate::typing::TypedSymbol::*;

    pub const NIL: &TypedExpr<'static> = &Val(Nil);
    pub const CONS: &TypedExpr<'static> = &Val(Cons(Vec::new()));
    pub const CAR: &TypedExpr<'static> = &Val(Car);
    pub const CDR: &TypedExpr<'static> = &Val(Cdr);
    pub const BCOMB: &TypedExpr<'static> = &Val(BComb(Vec::new()));
    pub const CCOMB: &TypedExpr<'static> = &Val(CComb(Vec::new()));
    pub const ICOMB: &TypedExpr<'static> = &Val(IComb);
    pub const SUM: &TypedExpr<'static> = &Val(Sum(Vec::new()));
    pub const NEG: &TypedExpr<'static> = &Val(Neg);
    pub const DIV: &TypedExpr<'static> = &Val(Div(Vec::new()));
    pub const LESS: &TypedExpr<'static> = &Val(Less(Vec::new()));
    pub const EQ: &TypedExpr<'static> = &Val(BigEq(Vec::new()));
    pub const T: &TypedExpr<'static> = &Val(True(Vec::new()));
    pub const F: &TypedExpr<'static> = &Val(False(Vec::new()));
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

    pub fn get_val(&'a self, symbol: TypedSymbol<'a>) -> ExprNode<'a> {
        self.exprs.alloc(TypedExpr::Val(symbol))
    }

    pub fn get_number(&'a self, v: i128) -> ExprNode<'a> {
        self.exprs.alloc(TypedExpr::Val(TypedSymbol::Number(v)))
    }

    #[allow(dead_code)]
    fn div(&'a self, e1: ExprNode<'a>, e2: ExprNode<'a>) -> ExprNode<'a> {
        let e3 = self.exprs.alloc(TypedExpr::Apply(DIV, e1));
        self.exprs.alloc(TypedExpr::Apply(e3, e2))
    }

    pub fn peel(
        &'a self,
        expr: ExprNode<'a>,
        vars: &HashMap<i128, ExprNode<'a>>,
        env: &mut HashMap<ExprNode<'a>, ExprNode<'a>>,
    ) -> Result<ExprNode, EvalError> {
        use TypedExpr::*;
        use TypedSymbol::*;
        if let Some(evaluated) = env.get(&expr) {
            return Ok(evaluated);
        }
        let result = match expr {
            Val(Cons(xs)) => {
                let args = xs
                    .iter()
                    .map(|&x| {
                        let e = self.eval(x, vars, env).unwrap();
                        let result = self.peel(e, vars, env).unwrap();
                        // env.insert(x, result);
                        result
                    })
                    .collect();
                self.get_val(Cons(args))
            }
            _ => expr,
        };
        env.insert(expr, result);
        Ok(result)
    }

    pub fn get_cons(&'a self, e1: ExprNode<'a>, e2: ExprNode<'a>) -> ExprNode<'a> {
        let e3 = self.exprs.alloc(TypedExpr::Apply(CONS, e1));
        self.exprs.alloc(TypedExpr::Apply(e3, e2))
    }

    pub fn eval2(
        &'a self,
        expr: ExprNode<'a>,
        vars: &HashMap<i128, ExprNode<'a>>,
    ) -> Result<ExprNode, EvalError> {
        let mut env = HashMap::new();
        let start = Instant::now();
        let expr = self.optimize(expr, vars, &mut HashSet::new())?;
        println!("optimize expr: {} ms", start.elapsed().as_millis());
        let expr = self.eval(expr, vars, &mut env)?;
        println!("eval expr: {} ms", start.elapsed().as_millis());
        // println!("{}", env.keys().len());
        let result = self.peel(expr, vars, &mut env);
        println!("peel expr: {} ms", start.elapsed().as_millis());
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
                        Ok(T)
                    }
                    Val(_) => {
                        Ok(expr)
                    }
                    Apply(Val(Sum(xs)), Val(Number(i))) if xs.len() == 0 => {
                        if let Val(Number(j)) = x {
                            Ok(self.get_number(i+j))
                        } else {
                            Ok(expr)
                        }
                    }
                    Apply(Val(Div(xs)), Val(Number(i))) if xs.len() == 0 => {
                        if let Val(Number(j)) = x {
                            Ok(self.get_number(i/j))
                        } else {
                            Ok(expr)
                        }
                    }
                    Apply(Val(Prod(xs)), Val(Number(i))) if xs.len() == 0 => {
                        if let Val(Number(j)) = x {
                            Ok(self.get_number(i*j))
                        } else {
                            Ok(expr)
                        }
                    }
                    Apply(Val(Less(xs)), Val(Number(i))) if xs.len() == 0 => {
                        if let Val(Number(j)) = x {
                            if i < j {
                                Ok(T)
                            } else {
                                Ok(F)
                            }
                        } else {
                            Ok(expr)
                        }
                    }
                    Apply(Val(BigEq(xs)), Val(Number(i))) if xs.len() == 0 => {
                        if let Val(Number(j)) = x {
                            if i == j {
                                Ok(T)
                            } else {
                                Ok(F)
                            }
                        } else {
                            Ok(expr)
                        }
                    }
                    _ => Ok(expr)
                }
            }
        }
    }

    fn eval(
        &'a self,
        expr: ExprNode<'a>,
        vars: &HashMap<i128, ExprNode<'a>>,
        env: &mut HashMap<ExprNode<'a>, ExprNode<'a>>,
    ) -> Result<ExprNode, EvalError> {
        use EvalError::*;
        use TypedExpr::*;
        use TypedSymbol::*;

        // println!("evaluating {:?}", expr);

        if let Some(evaluated) = env.get(&expr) {
            return Ok(evaluated);
        }

        match expr {
            Val(Variable(i)) => {
                let body = vars.get(&i).ok_or(UndefinedVariable(*i))?;
                let body = self.eval(body, vars, env)?;
                // env.insert(expr.clone(), body);
                Ok(body)
            }
            Val(_) => Ok(expr),
            Apply(f, x) => {
                let func = self.eval(f, vars, env)?;
                match func {
                    // Car
                    Val(Car) => {
                        // ap car x   =   ap x t
                        let v = self.get_app(*x, T);
                        let res = self.eval(v, vars, env)?;
                        // env.insert(expr.clone(), res);
                        Ok(res)
                    }
                    // Cdr
                    Val(Cdr) => {
                        // ap cdr x2   =   ap x2 f
                        let v = self.get_app(*x, F);
                        let res = self.eval(v, vars, env)?;
                        // env.insert(expr.clone(), res);
                        Ok(res)
                    }
                    // Cons
                    Val(Cons(xs)) if xs.len() == 2 => {
                        // ap ap ap cons x0 x1 x2   =   ap ap x2 x0 x1
                        let v = self.get_app(self.get_app(*x, xs[0]), xs[1]);
                        let res = self.eval(v, vars, env)?;
                        Ok(res)
                    }
                    Val(Cons(xs)) => {
                        let mut args = xs.clone();
                        args.push(*x);
                        Ok(self.get_val(Cons(args)))
                    }
                    // B-Combinator
                    Val(BComb(xs)) if xs.len() == 2 => {
                        // ap ap ap b x0 x1 x2   =   ap x0 ap x1 x2
                        let v = self.get_app(xs[0], self.get_app(xs[1], *x));
                        let res = self.eval(v, vars, env)?;
                        env.insert(expr, res);
                        Ok(res)
                    }
                    Val(BComb(xs)) => {
                        assert!(xs.len() < 2);
                        let mut args = xs.clone();
                        args.push(*x);
                        Ok(self.get_val(BComb(args)))
                    }
                    // C-Combinator
                    Val(CComb(xs)) if xs.len() == 2 => {
                        // ap ap ap c x0 x1 x2   =   ap ap x0 x2 x1
                        let v = self.get_app(self.get_app(xs[0], *x), xs[1]);
                        let res = self.eval(v, vars, env)?;
                        env.insert(expr, res);
                        Ok(res)
                    }
                    Val(CComb(xs)) => {
                        assert!(xs.len() < 2);
                        let mut args = xs.clone();
                        args.push(*x);
                        Ok(self.get_val(CComb(args)))
                    }
                    // S-Combinator
                    Val(SComb(xs)) if xs.len() == 2 => {
                        // ap ap ap s x0 x1 x2   =   ap ap x0 x2 ap x1 x2
                        let v = self.get_app(self.get_app(xs[0], *x), self.get_app(xs[1], *x));
                        let res = self.eval(v, vars, env)?;
                        env.insert(expr, res);
                        Ok(res)
                    }
                    Val(SComb(xs)) => {
                        assert!(xs.len() < 2);
                        let mut args = xs.clone();
                        args.push(*x);
                        Ok(self.get_val(SComb(args)))
                    }
                    // I-Combinator
                    Val(IComb) => {
                        // ap i x0   =   x0
                        let res = self.eval(*x, vars, env)?;
                        env.insert(expr, res);
                        Ok(res)
                    }
                    // True
                    Val(True(xs)) if xs.len() == 1 => {
                        // ap ap t x0 x1   =   x0
                        let x0 = xs[0];
                        self.eval(x0, vars, env)
                    }
                    Val(True(xs)) => {
                        assert_eq!(xs.len(), 0);
                        let mut args = xs.clone();
                        args.push(*x);
                        Ok(self.get_val(True(args)))
                    }
                    // False
                    Val(False(xs)) if xs.len() == 1 => {
                        // ap ap f x0 x1   =   x1
                        self.eval(*x, vars, env)
                    }
                    Val(False(xs)) => {
                        assert_eq!(xs.len(), 0);
                        let mut args = xs.clone();
                        args.push(*x);
                        Ok(self.get_val(False(args)))
                    }
                    // Sum (Add)
                    Val(Sum(xs)) if xs.len() == 1 => {
                        let x0 = self.eval(xs[0], vars, env)?.get_number().unwrap();
                        let x1 = self.eval(*x, vars, env)?.get_number().unwrap();
                        Ok(self.get_val(Number(x0 + x1)))
                    }
                    Val(Sum(xs)) => {
                        assert_eq!(xs.len(), 0);
                        let args = vec![*x];
                        Ok(self.get_val(Sum(args)))
                    }
                    // Product
                    Val(Prod(xs)) if xs.len() == 1 => {
                        let x0 = self.eval(xs[0], vars, env)?.get_number().unwrap();
                        let x1 = self.eval(*x, vars, env)?.get_number().unwrap();
                        let result = self.get_val(Number(x0 * x1));
                        env.insert(expr, result);
                        Ok(result)
                    }
                    Val(Prod(xs)) => {
                        assert_eq!(xs.len(), 0);
                        let args = vec![*x];
                        Ok(self.get_val(Prod(args)))
                    }
                    Val(Neg) => {
                        let x = self.eval(*x, vars, env)?;
                        let x = x.get_number().unwrap();
                        Ok(self.get_val(Number(-x)))
                    }
                    // Div
                    Val(Div(xs)) if xs.len() == 1 => {
                        let x_num = self.eval(xs[0], vars, env)?.get_number().unwrap();
                        let x_den = self.eval(*x, vars, env)?.get_number().unwrap();
                        let result = self.get_val(Number(x_num / x_den));
                        env.insert(expr, result);
                        Ok(result)
                    }
                    Val(Div(xs)) => {
                        assert_eq!(xs.len(), 0);
                        let args = vec![*x];
                        Ok(self.get_val(Div(args)))
                    }
                    Val(Nil) => Ok(T),
                    Val(IsNil) => {
                        let e = self.eval(*x, vars, env)?;
                        match e {
                            Val(Nil) => Ok(T),
                            Val(Cons(_)) => Ok(F),
                            _ => Err(ListIsExpected(e)),
                        }
                    }
                    // Less
                    Val(Less(xs)) if xs.len() == 1 => {
                        let x0 = self.eval(xs[0], vars, env)?.get_number().unwrap();
                        let x1 = self.eval(*x, vars, env)?.get_number().unwrap();

                        let result = if x0 < x1 {
                            T
                        } else {
                            F
                        };
                        env.insert(expr, result);
                        Ok(result)
                    }
                    Val(Less(xs)) => {
                        assert_eq!(xs.len(), 0);
                        let args = vec![*x];
                        Ok(self.get_val(Less(args)))
                    }
                    // BigEq
                    Val(BigEq(xs)) if xs.len() == 1 => {
                        let x0 = self.eval(xs[0], vars, env)?.get_number().unwrap();
                        let x1 = self.eval(*x, vars, env)?.get_number().unwrap();

                        let result = if x0 == x1 {
                            T
                        } else {
                            F
                        };
                        env.insert(expr, result);
                        Ok(result)
                    }
                    Val(BigEq(xs)) => {
                        assert_eq!(xs.len(), 0);
                        let args = vec![*x];
                        Ok(self.get_val(BigEq(args)))
                    }
                    _ => {
                        eprintln!("Applying f={:?} to x={:?}", &f, &x);
                        Err(Todo)
                    }
                }
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

    fn empty_env<'a>() -> HashMap<i128, ExprNode<'a>> {
        HashMap::new()
    }

    #[test]
    fn test_div_numerator_minus() {
        let eval = Evaluator::new();
        // ap ap div -5 3   =   -1
        let exp = eval.div(eval.get_number(-5), eval.get_number(3));
        let e = eval.eval2(exp, &empty_env()).unwrap();
        assert_eq!(e, eval.get_number(-1))
    }

    #[test]
    fn test_variable_func() {
        use TypedExpr::*;
        use TypedSymbol::*;
        let mut eval = Evaluator::new();
        // var1 = cons
        // ap ap cons 0 ap ap var1 1 2
        let mut env = HashMap::new();
        let v = eval.get_val(Cons(vec![]));
        env.insert(1, v);
        let v1 = eval.get_val(Variable(1));
        let n1 = eval.get_number(1);
        let e2 = eval.get_app(v1, n1);
        let n2 = eval.get_number(2);
        let e3 = eval.get_app(e2, n2);
        let n0 = eval.get_number(0);
        let e = eval.get_cons(n0, e3);

        let tmp = eval.get_val(Cons(vec![n1, n2]));
        let expected = Val(Cons(vec![n0, tmp]));

        assert_eq!(&expected, eval.eval2(&e, &env).unwrap());
    }

    #[test]
    fn test_comb_b() {
        // B neg neg x = x
        for x in -3..4 {
            let mut eval = Evaluator::new();
            let expr = eval.get_app(
                eval.get_app(eval.get_app(BCOMB, NEG), NEG),
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
            let expr = eval.get_app(ICOMB, NEG);
            let mut env = HashMap::new();
            assert_eq!(NEG, eval.eval(&expr, &mut env, &mut HashMap::new()).unwrap());
        }
        {
            let mut eval = Evaluator::new();
            let expr = eval.get_app(ICOMB, BCOMB);
            let mut env = HashMap::new();
            assert_eq!(BCOMB, eval.eval2(&expr, &mut env).unwrap());
        }
    }
}
