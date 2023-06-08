use super::*;
use super::re::{ReTrie};

use std::cell::{RefCell};

fn parser<'t>(t: &'t ReTrie<Token>, x: &'static str) -> ExpParser<'t, 'static> {
  let tokens = Tokenizer::new(t, x);
  ExpParser::new(tokens)
}

#[allow(unused_variables)]
fn build_testcases<'t>(t: &'t ReTrie<Token>) -> Vec<(bool, bool, &'static str, ExpParser<'t, 'static>, Option<Result<Exp, ExpError>>)> {
  let xys = RefCell::new(Vec::new());
  let x_ = |x: &'static str| {
    xys.borrow_mut().push((false, false, x, parser(&t, x), None));
  };
  let error_x_ = |x: &'static str| {
    xys.borrow_mut().push((false, true, x, parser(&t, x), None));
  };
  let error_xe = |x: &'static str, e: ExpError| {
    xys.borrow_mut().push((false, true, x, parser(&t, x), Some(Err(e))));
  };
  let trace_x_ = |x: &'static str| {
    xys.borrow_mut().push((true, false, x, parser(&t, x), None));
  };
  let xy = |x: &'static str, y: Exp| {
    xys.borrow_mut().push((false, false, x, parser(&t, x), Some(Ok(y))));
  };
  let xe = |x: &'static str, e: ExpError| {
    xys.borrow_mut().push((false, false, x, parser(&t, x), Some(Err(e))));
  };
  x_(r"(\x -> let y = -x in y)");
  x_(r" \x -> let y = -x in y ");
  x_(r" \x -> -x ");
  error_xe(r" \x -> - "
          ,   ExpError::Eof);
  error_xe(r" \x -> x + "
          ,   ExpError::Eof);
  error_xe(r" \x -> ( x + ) "
          ,   ExpError::Expected(Token::RParen, Token::Plus));
  x_(r" \x -> x - x ");
  x_(r" \x -> x-x ");
  x_(r" \x -> x + - x ");
  x_(r" \x -> x + -x ");
  x_(r" \x -> x+-x ");
  x_(r" \x -> x * x - x ");
  x_(r" \x -> x * x -x ");
  x_(r" \x -> x*x-x ");
  x_(r" \x -> x * - x - x ");
  x_(r" \x -> x * -x - x ");
  x_(r" \x -> x*-x-x ");
  x_(r" \x -> x * - x x ");
  x_(r" \x -> x * -x x ");
  x_(r" \x -> x*-x x ");
  x_(r" \x -> x x + x ");
  x_(r" \x -> x + x x ");
  x_(r" \x -> x x ");
  x_(r" \x -> x x x ");
  x_(r" \x -> x x x x ");
  x_(r" \x -> x (x x x) ");
  x_(r" \x -> x (x (x x)) ");
  x_(r" \x -> x (x (x x) (x x)) ");
  x_(r" \x -> x (x (x (x x)) (x (x x))) ");
  x_(r" \x -> x + x * x x ");
  x_(r" \x -> x + x * x (x) ");
  x_(r" \x -> x + x * x(x) ");
  x_(r" \x -> x + x * (x)x ");
  x_(r" \x -> x + x * (x) x ");
  x_(r" \x -> x + x x * x ");
  x_(r" \x -> x x + x * x ");
  x_(r" \x -> x x * x + x ");
  x_(r" \x -> x x x + x ");
  x_(r" \x -> x + x x x * x ");
  x_(r" \x -> x * x x x + x ");
  x_(r" \x -> x + x * x - x ");
  x_(r" \x -> x + x `add` x ");
  x_(r" \x -> (x + x) `add` x ");
  x_(r" \x -> x + (x `add` x) ");
  x_(r" \x -> (\t -> t)x ");
  x_(r" \x -> (+) x x ");
  x_(r" \x -> (+ x) x x ");
  x_(r" \x -> (+ (x)) x x ");
  x_(r" \x -> (+ x x) x x ");
  x_(r" \x -> (+ (x) x) x x ");
  x_(r" \x -> (+ x (x)) x x ");
  x_(r" \x -> (+ (x x)) x x ");
  x_(r" \x -> (-) x x ");
  x_(r" \x -> (- x) x x ");
  x_(r" \x -> (-x)x x ");
  x_(r" \x -> (- - x) x x ");
  x_(r" \x -> (--x)x x ");
  x_(r" \x -> (- x x) x x ");
  x_(r" \x -> (-x x)x x ");
  x_(r" \x -> ((-x) x)x x ");
  x_(r" \x -> (x - x) x x ");
  x_(r" \x -> (x-x)x x ");
  x_(r" \x -> (x(-x))x x ");
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
      if let Some(_y) = y {
        unimplemented!();
        //println!("    y = {:?}", y.unwrap());
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
