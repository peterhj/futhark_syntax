use super::*;
use super::re::{ReTrie};

fn parser<'t>(t: &'t ReTrie<Token>, x: &'static str) -> ExpParser<'t, 'static> {
  let tokens = Tokenizer::new(t, x);
  ExpParser::new(tokens)
}

fn build_testcases<'t>(t: &'t ReTrie<Token>) -> Vec<(&'static str, ExpParser<'t, 'static>, ())> {
  let mut ts = Vec::new();
  let mut t_ = |x: &'static str| {
    ts.push((x, parser(&t, x), ()));
  };
  t_(r"(\x -> let y = x + x * x x in y)");
  t_(r"\x -> let y = x + x * x x in y");
  t_(r"\x -> let y = x + x x * x in y");
  t_(r"\x -> let y = x x + x * x in y");
  t_(r"\x -> let y = x x * x + x in y");
  t_(r"\x -> let y = x x x + x in y");
  t_(r"\x -> let y = x + x x x * x in y");
  t_(r"\x -> let y = x * x x x + x in y");
  t_(r"\x -> let y = x + x * x - x in y");
  t_(r"\x -> let y = -x in y");
  t_(r"\x -> let y = x + -x in y");
  t_(r"\x -> let y = x + - x in y");
  t_(r"\x -> let y = x * -x - x in y");
  t_(r"\x -> let y = x x + x in y");
  t_(r"\x -> let y = x + x x in y");
  t_(r"\x -> let y = x x in y");
  t_(r"\x -> let y = x x x in y");
  t_(r"\x -> let y = x x x x in y");
  t_(r" \x -> let y = x x x x in y ");
  t_(r" \x -> let y = x + x `add` x in y ");
  t_(r" \x -> let y = x + (x `add` x) in y ");
  t_(r" \x -> let y = (x + x) `add` x in y ");
  t_(r" \x -> let y = (\t -> t)x in y ");
  t_(r" \x -> let y = (+) x x in y ");
  t_(r" \x -> let y = (+ x) x x in y ");
  t_(r" \x -> let y = (+ x x) x x in y ");
  ts
}

#[test]
fn testcases() {
  let trie = tokenizer_trie();
  let testcases = build_testcases(&trie);
  let mut errs = 0;
  for (x, parser, _y) in testcases.into_iter() {
    let result = parser.parse();
    if result.is_ok() {
      println!("OK: \"{}\"", x);
    } else {
      println!("ERROR: \"{}\"", x);
      errs += 1;
    }
  }
  if errs > 0 {
    panic!("FAILED: {} parse errors", errs);
  }
}
