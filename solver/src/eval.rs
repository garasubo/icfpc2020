use std::collections::HashMap;

use crate::typing::*;

#[derive(Debug)]
pub enum EvalError {
    NumberIsExpected(TypedExpr),
    ListIsExpected(TypedExpr),
    UndefinedVariable(i128),
    Todo,
}

fn generate_new_var_id(memo: &HashMap<i128, TypedExpr>) -> i128 {
    -(memo.len() as i128)
}

pub fn eval(
    expr: &TypedExpr,
    mut env: &mut HashMap<i128, TypedExpr>,
    strict: bool,
) -> Result<TypedExpr, EvalError> {
    use crate::typing::raku::*;
    use EvalError::*;
    use TypedExpr::*;
    use TypedSymbol::*;

    match expr {
        Val(Variable(i)) => {
            let v = env.get(i).map(|v| v.clone()).ok_or(UndefinedVariable(*i))?;
            let val = eval(&v, &mut env, false)?;
            *env.get_mut(i).unwrap() = val.clone();
            Ok(val)
        }
        Val(Cons(args)) if strict => {
            let args: Vec<TypedExpr> = args
                .iter()
                .map(|v| eval(&v, &mut env, true).unwrap())
                .collect();
            Ok(Val(Cons(args.clone())))
        }
        Val(_) => Ok(expr.clone()),
        Apply(f, x) => {
            let f = eval(&f, env, strict)?;
            let x = if strict {
                eval(&x, &mut env, strict)?
            } else {
                *x.clone()
            };
            match f {
                // Car
                Val(Car) => {
                    // ap car x   =   ap x t
                    let v = app(x, val(True(vec![])));
                    eval(&v, &mut env, strict)
                }
                // Cdr
                Val(Cdr) => {
                    // ap cdr x2   =   ap x2 f
                    let v = app(x, val(False(vec![])));
                    eprintln!("cdr v = {:?}", &v);
                    eval(&v, &mut env, strict)
                }
                // Cons
                Val(Cons(xs)) if xs.len() == 2 => {
                    // ap ap ap cons x0 x1 x2   =   ap ap x2 x0 x1
                    let v = app(app(x, xs[0].clone()), xs[1].clone());
                    eval(&v, &mut env, strict)
                }
                Val(Cons(xs)) => {
                    let mut args = xs.clone();
                    args.push(x);
                    Ok(Val(Cons(args)))
                }
                // B-Combinator
                Val(BComb(xs)) if xs.len() == 2 => {
                    // ap ap ap b x0 x1 x2   =   ap x0 ap x1 x2
                    let v = app(xs[0].clone(), app(xs[1].clone(), x));
                    eval(&v, &mut env, strict)
                }
                Val(BComb(xs)) => {
                    assert!(xs.len() < 2);
                    let mut args = xs.clone();
                    args.push(x);
                    Ok(Val(BComb(args)))
                }
                // C-Combinator
                Val(CComb(xs)) if xs.len() == 2 => {
                    // ap ap ap c x0 x1 x2   =   ap ap x0 x2 x1
                    let v = app(app(xs[0].clone(), x), xs[1].clone());
                    eval(&v, &mut env, strict)
                }
                Val(CComb(xs)) => {
                    assert!(xs.len() < 2);
                    let mut args = xs.clone();
                    args.push(x);
                    Ok(Val(CComb(args)))
                }
                // S-Combinator
                Val(SComb(xs)) if xs.len() == 2 => {
                    // ap ap ap s x0 x1 x2   =   ap ap x0 x2 ap x1 x2
                    let id = generate_new_var_id(&env);
                    let var = Val(Variable(id));
                    env.insert(id, x);
                    let v = app(app(xs[0].clone(), var.clone()), app(xs[1].clone(), var));
                    eval(&v, &mut env, strict)
                }
                Val(SComb(xs)) => {
                    assert!(xs.len() < 2);
                    let mut args = xs.clone();
                    args.push(x);
                    Ok(Val(SComb(args)))
                }
                // I-Combinator
                Val(IComb) => {
                    // ap i x0   =   x0
                    eval(&x, &mut env, strict)
                }
                // True
                Val(True(xs)) if xs.len() == 1 => {
                    // ap ap t x0 x1   =   x0
                    let x0 = xs[0].clone();
                    eval(&x0, &mut env, strict)
                }
                Val(True(xs)) => {
                    assert_eq!(xs.len(), 0);
                    let mut args = xs.clone();
                    args.push(x);
                    Ok(Val(True(args)))
                }
                // False
                Val(False(xs)) if xs.len() == 1 => {
                    // ap ap f x0 x1   =   x1
                    eval(&x, &mut env, strict)
                }
                Val(False(xs)) => {
                    assert_eq!(xs.len(), 0);
                    let mut args = xs.clone();
                    args.push(x);
                    Ok(Val(False(args)))
                }
                // Sum (Add)
                Val(Sum(xs)) if xs.len() == 1 => {
                    let x0 = eval(&xs[0], &mut env, strict)?.get_number().unwrap();
                    let x1 = eval(&x, &mut env, strict)?.get_number().unwrap();
                    Ok(Val(Number(x0 + x1)))
                }
                Val(Sum(xs)) => {
                    assert_eq!(xs.len(), 0);
                    let args = vec![x];
                    Ok(Val(Sum(args)))
                }
                // Product
                Val(Prod(xs)) if xs.len() == 1 => {
                    let x0 = eval(&xs[0], &mut env, strict)?.get_number().unwrap();
                    let x1 = eval(&x, &mut env, strict)?.get_number().unwrap();
                    Ok(Val(Number(x0 * x1)))
                }
                Val(Prod(xs)) => {
                    assert_eq!(xs.len(), 0);
                    let args = vec![x];
                    Ok(Val(Prod(args)))
                }
                Val(Neg) => {
                    let x = eval(&x, &mut env, strict)?;
                    let x = x.get_number().unwrap();
                    Ok(Val(Number(-x)))
                }
                // Div
                Val(Div(xs)) if xs.len() == 1 => {
                    let x_num = eval(&xs[0], &mut env, strict)?.get_number().unwrap();
                    let x_den = eval(&x, &mut env, strict)?.get_number().unwrap();
                    Ok(Val(Number(x_num / x_den)))
                }
                Val(Div(xs)) => {
                    assert_eq!(xs.len(), 0);
                    let args = vec![x];
                    Ok(Val(Div(args)))
                }
                Val(Nil) => Ok(Val(True(vec![]))),
                Val(IsNil) => {
                    let e = eval(&x, &mut env, strict)?;
                    match e {
                        Val(Nil) => Ok(Val(True(vec![]))),
                        Val(Cons(_)) => Ok(Val(False(vec![]))),
                        _ => Err(ListIsExpected(e)),
                    }
                }
                // Less
                Val(Less(xs)) if xs.len() == 1 => {
                    let x0 = eval(&xs[0], &mut env, strict)?.get_number().unwrap();
                    let x1 = eval(&x, &mut env, strict)?.get_number().unwrap();

                    if x0 < x1 {
                        Ok(Val(True(vec![])))
                    } else {
                        Ok(Val(False(vec![])))
                    }
                }
                Val(Less(xs)) => {
                    assert_eq!(xs.len(), 0);
                    let args = vec![x];
                    Ok(Val(Less(args)))
                }
                // BigEq
                Val(BigEq(xs)) if xs.len() == 1 => {
                    let x0 = eval(&xs[0], &mut env, strict)?.get_number().unwrap();
                    let x1 = eval(&x, &mut env, strict)?.get_number().unwrap();

                    if x0 == x1 {
                        Ok(Val(True(vec![])))
                    } else {
                        Ok(Val(False(vec![])))
                    }
                }
                Val(BigEq(xs)) => {
                    assert_eq!(xs.len(), 0);
                    let args = vec![x];
                    Ok(Val(BigEq(args)))
                }
                _ => {
                    eprintln!("Applying f={:?} to x={:?}", &f, &x);
                    Err(Todo)
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::typing::raku::*;
    use crate::typing::TypedExpr::*;
    use crate::typing::TypedSymbol::*;

    fn empty_env() -> HashMap<i128, TypedExpr> {
        HashMap::new()
    }

    #[test]
    fn test_neg() {
        let exp = neg(number(5));
        let e = eval(&exp, &mut empty_env(), false).unwrap();
        assert_eq!(e, number(-5))
    }

    #[test]
    fn test_div() {
        let exp = div(number(5), number(2));
        let e = eval(&exp, &mut empty_env(), false).unwrap();
        assert_eq!(e, number(2))
    }

    #[test]
    fn test_div_numerator_minus() {
        // ap ap div -5 3   =   -1
        let exp = div(number(-5), number(3));
        let e = eval(&exp, &mut empty_env(), false).unwrap();
        assert_eq!(e, number(-1))
    }

    #[test]
    fn test_div_denominator_minus() {
        // ap ap div 5 -3   =   -1
        let exp = div(number(5), number(-3));
        let e = eval(&exp, &mut empty_env(), false).unwrap();
        assert_eq!(e, number(-1))
    }

    #[test]
    fn test_div_num_den_minus() {
        // ap ap div -5 -3   =   1
        let exp = div(number(-5), number(-3));
        let e = eval(&exp, &mut empty_env(), false).unwrap();
        assert_eq!(e, number(1))
    }

    #[test]
    fn test_less() {
        use TypedExpr::Val;

        // ap ap lt 0 -1   =   f
        let exp0 = less(number(0), number(-1));
        let e0 = eval(&exp0, &mut empty_env(), false).unwrap();
        assert_eq!(e0, Val(TypedSymbol::False(vec![])));

        // ap ap lt 0 0   =   f
        let exp1 = less(number(0), number(0));
        let e1 = eval(&exp1, &mut empty_env(), false).unwrap();
        assert_eq!(e1, Val(TypedSymbol::False(vec![])));

        // ap ap lt 0 1   =   t
        let exp2 = less(number(0), number(1));
        let e2 = eval(&exp2, &mut empty_env(), false).unwrap();
        assert_eq!(e2, Val(TypedSymbol::True(vec![])));
    }

    #[test]
    fn test_cons() {
        {
            let pair = cons(number(1), NIL);
            let x = app(CAR, pair);
            let e = eval(&x, &mut empty_env(), false).unwrap();
            assert_eq!(e, number(1));
        }
        {
            let pair = cons(number(1), NIL);
            let x = app(CDR, pair);
            let e = eval(&x, &mut empty_env(), false).unwrap();
            assert_eq!(e, NIL);
        }
        {
            let x = cons(number(1), cons(number(2), NIL));
            let e = eval(&x, &mut empty_env(), false).unwrap();
            assert_eq!(e, val(Cons(vec![number(1), cons(number(2), NIL)])));
        }
        {
            let x = cons(number(1), cons(number(2), NIL));
            let x = app(CDR, x);
            let e = eval(&x, &mut empty_env(), false).unwrap();
            assert_eq!(e, val(Cons(vec![number(2), NIL])));
        }
    }

    #[test]
    fn test_cons_galaxy_line1() {
        use TypedSymbol::*;

        // ap ap cons 7 ap ap cons 123 nil
        let x = cons(number(7), cons(number(123), NIL));

        let expected = val(Cons(vec![
            val(Number(7)),
            app(app(val(Cons(vec![])), val(Number(123))), val(Nil)),
        ]));

        assert_eq!(expected, eval(&x, &mut empty_env(), false).unwrap());
    }

    #[test]
    fn test_variable() {
        use TypedExpr::*;
        use TypedSymbol::*;
        // var1 = 123
        // ap ap cons 0 ap ap cons var1 2
        let mut env = HashMap::new();
        env.insert(1, number(123));
        let e = cons(number(0), cons(variable(1), number(2)));
        let expected = Val(Cons(vec![
            Val(Number(0)),
            app(app(val(Cons(vec![])), val(Variable(1))), val(Number(2))),
        ]));

        assert_eq!(expected, eval(&e, &mut env, false).unwrap());
    }

    #[test]
    fn test_variable_func() {
        use TypedExpr::*;
        use TypedSymbol::*;
        // var1 = cons
        // ap ap cons 0 ap ap var1 1 2
        let mut env = HashMap::new();
        env.insert(1, Val(Cons(vec![])));
        let e = cons(number(0), app(app(variable(1), number(1)), number(2)));
        let expected = Val(Cons(vec![
            Val(Number(0)),
            app(app(val(Variable(1)), val(Number(1))), val(Number(2))),
        ]));

        assert_eq!(expected, eval(&e, &mut env, false).unwrap());
    }

    #[test]
    fn test_variable_func_with_var() {
        use TypedExpr::*;
        use TypedSymbol::*;
        // var1 = cons 1
        // ap ap cons 0 ap var1 2
        let mut env = HashMap::new();
        env.insert(1, Val(Cons(vec![Val(Number(1))])));
        let e = cons(number(0), app(variable(1), number(2)));
        let expected = Val(Cons(vec![
            Val(Number(0)),
            app(val(Variable(1)), val(Number(2))),
        ]));

        assert_eq!(expected, eval(&e, &mut env, false).unwrap());
    }

    #[test]
    fn test_sum() {
        let mut env = HashMap::new();
        let expr = sum(number(1), number(2));
        assert_eq!(number(3), eval(&expr, &mut env, false).unwrap());
    }

    #[test]
    fn test_is_nil() {
        let mut env = HashMap::new();
        let expr = isnil(NIL);
        assert_eq!(T, eval(&expr, &mut env, false).unwrap());
        let expr = isnil(cons(number(1), NIL));
        assert_eq!(F, eval(&expr, &mut env, false).unwrap());
    }

    #[test]
    fn test_big_eq() {
        let mut env = HashMap::new();
        let expr = big_eq(number(1), number(1));
        assert_eq!(T, eval(&expr, &mut env, false).unwrap());
        let expr = big_eq(number(1), number(0));
        assert_eq!(F, eval(&expr, &mut env, false).unwrap());
    }

    #[test]
    fn test_comb_c() {
        // C add 2 3 = add 3 2 = 5
        {
            let expr = app(app(app(CCOMB, SUM), number(2)), number(3));
            let mut env = HashMap::new();
            assert_eq!(number(5), eval(&expr, &mut env, false).unwrap());
        }
        // C cons 2 3 = cons 3 2 = 5
        {
            let expr = app(app(app(CCOMB, CONS), number(2)), number(3));
            let mut env = HashMap::new();
            assert_eq!(
                Val(Cons(vec![number(3), number(2)])),
                eval(&expr, &mut env, false).unwrap()
            );
        }
    }

    #[test]
    fn test_comb_b() {
        // B neg neg x = x
        for x in -3..4 {
            let expr = app(app(app(BCOMB, NEG), NEG), number(x));
            let mut env = HashMap::new();
            assert_eq!(number(x), eval(&expr, &mut env, false).unwrap());
        }
    }

    #[test]
    fn test_comb_i() {
        // I x = x
        {
            let expr = app(ICOMB, NEG);
            let mut env = HashMap::new();
            assert_eq!(NEG, eval(&expr, &mut env, false).unwrap());
        }
        {
            let expr = app(ICOMB, BCOMB);
            let mut env = HashMap::new();
            assert_eq!(BCOMB, eval(&expr, &mut env, false).unwrap());
        }
    }
}
