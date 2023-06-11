use super::*;
use super::re::{ReTrie};

use std::cell::{RefCell};

fn parser<'t>(t: &'t ReTrie<Token>, x: &'static str) -> ExpParser<'t, 'static> {
  let tokens = Tokenizer::new(t, x);
  ExpParser::new(tokens)
}

#[allow(unused_variables)]
fn build_testcases<'t>(t: &'t ReTrie<Token>) -> Vec<(bool, bool, &'static str, ExpParser<'t, 'static>, Option<Result<ExpRef, ExpError>>)> {
  let xys = RefCell::new(Vec::new());
  let x_ = |x: &'static str| {
    xys.borrow_mut().push((false, false, x, parser(&t, x), None));
  };
  let error_x_ = |x: &'static str| {
    xys.borrow_mut().push((false, true, x, parser(&t, x), None));
  };
  let trace_x_ = |x: &'static str| {
    xys.borrow_mut().push((true, false, x, parser(&t, x), None));
  };
  let xe = |x: &'static str, e: ExpError| {
    xys.borrow_mut().push((false, true, x, parser(&t, x), Some(Err(e))));
  };
  let trace_xe = |x: &'static str, e: ExpError| {
    xys.borrow_mut().push((true, true, x, parser(&t, x), Some(Err(e))));
  };
  let xy = |x: &'static str, y: ExpRef| {
    xys.borrow_mut().push((false, false, x, parser(&t, x), Some(Ok(y))));
  };
  xy(r"(\x -> let y = -x in y)"
    ,   Exp::Lam(vec!["x".into()],
            Exp::Let("y".into(),
                Exp::Neg(
                    Exp::id("x").into()
                ).into(),
                Exp::id("y").into()
            ).into()
        ).into()
    );
  xy(r" \x -> let y = -x in y "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Let("y".into(),
                Exp::Neg(
                    Exp::id("x").into()
                ).into(),
                Exp::id("y").into()
            ).into()
        ).into()
    );
  xy(r" \x -> -x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Neg(
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xe(r" \x -> - "
    ,   ExpError::Eof);
  xe(r" \x -> x + "
    ,   ExpError::Eof);
  xe(r" \x -> ( x + ) "
    //,   ExpError::Expected(Token::RParen, Token::Plus)
    ,   ExpError::InvalidNud(Token::RParen));
  xy(r" \x -> x - x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::id("x").into(),
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xy(r" \x -> x-x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::id("x").into(),
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xy(r" \x -> x + - x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Add(
                Exp::id("x").into(),
                Exp::Neg(
                    Exp::id("x").into()
                ).into()
            ).into()
        ).into()
    );
  xy(r" \x -> x + -x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Add(
                Exp::id("x").into(),
                Exp::Neg(
                    Exp::id("x").into()
                ).into()
            ).into()
        ).into()
    );
  xy(r" \x -> x+-x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Add(
                Exp::id("x").into(),
                Exp::Neg(
                    Exp::id("x").into()
                ).into()
            ).into()
        ).into()
    );
  xy(r" \x -> x * x - x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::id("x").into()
                ).into(),
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xy(r" \x -> x * x -x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::id("x").into()
                ).into(),
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xy(r" \x -> x*x-x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::id("x").into()
                ).into(),
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xy(r" \x -> x * - x - x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::Neg(
                        Exp::id("x").into()
                    ).into()
                ).into(),
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xy(r" \x -> x * -x - x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::Neg(
                        Exp::id("x").into()
                    ).into()
                ).into(),
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xy(r" \x -> x*-x-x "
    ,   Exp::LamAlt(
            vec!["x".into()],
            Exp::Sub(
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::Neg(
                        Exp::id("x").into()
                    ).into(),
                ).into(),
                Exp::id("x").into()
            ).into()
        ).into()
    );
  xy(r" \x -> x * - x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Mul(
                Exp::id("x").into(),
                Exp::Neg(
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into()
                ).into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x * -x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Mul(
                Exp::id("x").into(),
                Exp::Neg(
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into()
                ).into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x*-x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Mul(
                Exp::id("x").into(),
                Exp::Neg(
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into()
                ).into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x x + x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Add(
                Exp::App(
                    Exp::id("x").into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x + x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Add(
                Exp::id("x").into(),
                Exp::App(
                    Exp::id("x").into(),
                    Exp::id("x").into(),
                ).into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::id("x").into(),
                Exp::id("x").into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::id("x").into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x x x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x (x x x) "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::id("x").into(),
                Exp::App(
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x (x (x x)) "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::id("x").into(),
                Exp::App(
                    Exp::id("x").into(),
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x (x (x x) (x x)) "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::id("x").into(),
                Exp::App(
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::App(
                            Exp::id("x").into(),
                            Exp::id("x").into(),
                        ).into(),
                    ).into(),
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x (x (x (x x)) (x (x x))) "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::id("x").into(),
                Exp::App(
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::App(
                            Exp::id("x").into(),
                            Exp::App(
                                Exp::id("x").into(),
                                Exp::id("x").into(),
                            ).into(),
                        ).into(),
                    ).into(),
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::App(
                            Exp::id("x").into(),
                            Exp::id("x").into(),
                        ).into(),
                    ).into(),
                ).into(),
            ).into()
        ).into()
    );
  xy(r" \x -> x - x * x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::id("x").into(),
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> x - x * x (x) "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::id("x").into(),
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> x - x * x(x) "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::id("x").into(),
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> x - x * (x)x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::id("x").into(),
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> x - x * (x) x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::id("x").into(),
                Exp::Mul(
                    Exp::id("x").into(),
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
            ).into(),
        ).into()
    );
  x_(r" \x -> x + x x * x ");
  x_(r" \x -> x x + x * x ");
  x_(r" \x -> x x * x + x ");
  x_(r" \x -> x x x + x ");
  x_(r" \x -> x + x x x * x ");
  x_(r" \x -> x * x x x + x ");
  xy(r" \x -> x - x * x + x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Add(
                Exp::Sub(
                    Exp::id("x").into(),
                    Exp::Mul(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> x + x * x - x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Sub(
                Exp::Add(
                    Exp::id("x").into(),
                    Exp::Mul(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> x + x `add` x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::InfixApp(
                InfixOp::Add,
                Exp::Add(
                    Exp::id("x").into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (x + x) `add` x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::InfixApp(
                InfixOp::Add,
                Exp::Add(
                    Exp::id("x").into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> x + (x `add` x) "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::Add(
                Exp::id("x").into(),
                Exp::InfixApp(
                    InfixOp::Add,
                    Exp::id("x").into(),
                    Exp::id("x").into(),
                ).into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (\t -> t)x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::Lam(vec!["t".into()],
                    Exp::id("t").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> \t -> t x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::LamAlt(vec!["t".into()],
                Exp::App(
                    Exp::id("t").into(),
                    Exp::id("x").into(),
                ).into(),
            ).into(),
        ).into()
    );
  x_(r" \x -> (+) x x ");
  x_(r" \x -> (+ x) x x ");
  x_(r" \x -> (+ (x)) x x ");
  x_(r" \x -> (+ x x) x x ");
  x_(r" \x -> (+ (x) x) x x ");
  x_(r" \x -> (+ x (x)) x x ");
  x_(r" \x -> (+ (x x)) x x ");
  xy(r" \x -> (-) x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::InfixOp(InfixOp::Sub).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (- x) x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::Neg(
                        Exp::id("x").into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (-x)x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::Neg(
                        Exp::id("x").into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (- - x) x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::Neg(
                        Exp::Neg(
                            Exp::id("x").into(),
                        ).into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (--x)x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::Neg(
                        Exp::Neg(
                            Exp::id("x").into(),
                        ).into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (- x x) x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::Neg(
                        Exp::App(
                            Exp::id("x").into(),
                            Exp::id("x").into(),
                        ).into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (-x x)x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::Neg(
                        Exp::App(
                            Exp::id("x").into(),
                            Exp::id("x").into(),
                        ).into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> ((-x) x)x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::App(
                        Exp::Neg(
                            Exp::id("x").into(),
                        ).into(),
                        Exp::id("x").into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (x - x) x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::Sub(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (x-x)x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::Sub(
                        Exp::id("x").into(),
                        Exp::id("x").into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x -> (x(-x))x x "
    ,   Exp::LamAlt(vec!["x".into()],
            Exp::App(
                Exp::App(
                    Exp::App(
                        Exp::id("x").into(),
                        Exp::Neg(
                            Exp::id("x").into(),
                        ).into(),
                    ).into(),
                    Exp::id("x").into(),
                ).into(),
                Exp::id("x").into(),
            ).into(),
        ).into()
    );
  xy(r" \x y -> x y "
    ,   Exp::LamAlt(vec!["x".into(), "y".into()],
            Exp::App(
                Exp::id("x").into(),
                Exp::id("y").into(),
            ).into(),
        ).into()
    );
  xy(r" \x y z -> x y z "
    ,   Exp::LamAlt(vec!["x".into(), "y".into(), "z".into()],
            Exp::App(
                Exp::App(
                    Exp::id("x").into(),
                    Exp::id("y").into(),
                ).into(),
                Exp::id("z").into(),
            ).into(),
        ).into()
    );
  xys.into_inner()
}

#[test]
fn testcases() {
  let trie = tokenizer_trie();
  let testcases = build_testcases(&trie);
  let mut n = 0;
  let mut fpos = 0;
  let mut fneg = 0;
  let mut mism = 0;
  for (trace, e, x, mut parser, y) in testcases.into_iter() {
    if trace {
      parser = parser.trace();
    }
    let result = parser.parse();
    // FIXME: compare result with reference exp.
    if !e && result.is_err() {
      println!("FALSE POS: x = \"{}\"", x);
      fpos += 1;
    } else if e && result.is_ok() {
      println!("FALSE NEG: x = \"{}\"", x);
      println!("           r = {:?}", result.unwrap());
      fneg += 1;
    } else if result.is_err() {
      let r = result.unwrap_err();
      if let Some(Ok(_)) = y {
        unimplemented!();
      } else if let Some(Err(ey)) = y {
        if r.0 != ey {
          println!("MISMATCH: x = \"{}\"", x);
          println!("          e = {:?}", r);
          println!("          y = {:?}", ey);
          mism += 1;
        } else {
          println!("POSITIVE: x = \"{}\"", x);
          println!("          e = {:?}", r);
          println!("          y = {:?}", ey);
        }
      } else {
        println!("POSITIVE: x = \"{}\"", x);
        println!("          e = {:?}", r);
      }
    } else if result.is_ok() {
      let r = result.unwrap();
      if let Some(Err(_)) = y {
        unimplemented!();
      } else if let Some(Ok(y)) = y {
        if &r != &*y {
          println!("MISMATCH: x = \"{}\"", x);
          println!("          r = {:?}", r);
          println!("          y = {:?}", y);
        } else {
          println!("OK: x = \"{}\"", x);
          println!("    r = {:?}", r);
          println!("    y = {:?}", y);
        }
      } else {
        println!("OK: x = \"{}\"", x);
        println!("    r = {:?}", r);
      }
    } else {
      unreachable!();
    }
    n += 1;
  }
  if fpos > 0 || fneg > 0 || mism > 0 {
    println!("FAILED: {}/{} false positives, {}/{} false negatives, {}/{} mismatches, out of {} total",
        fpos, n, fneg, n, mism, n, n);
    panic!();
  } else {
    println!("PASSED: {} total", n);
  }
}
