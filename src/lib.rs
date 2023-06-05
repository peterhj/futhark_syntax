extern crate regex_syntax;
extern crate smol_str;

use crate::re::{ReTrie};

use regex_syntax::{Parser as ReParser};
use regex_syntax::hir::{Hir as ReExp};
use smol_str::{SmolStr};

use std::cmp::{Ordering, max, min};
use std::iter::{Peekable};
use std::rc::{Rc};

pub mod re;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default, Debug)]
pub struct Pos {
  pub line: usize,
  pub col:  usize,
}

impl PartialOrd for Pos {
  fn partial_cmp(&self, rhs: &Pos) -> Option<Ordering> {
    Some(self.cmp(rhs))
  }
}

impl Ord for Pos {
  fn cmp(&self, rhs: &Pos) -> Ordering {
    let ret = self.line.cmp(&rhs.line);
    match ret {
      Ordering::Equal => self.col.cmp(&rhs.col),
      _ => ret
    }
  }
}

#[derive(Clone, Copy, Default, Debug)]
pub struct Span {
  pub start: Pos,
  pub end: Pos,
}

impl Span {
  pub fn point(p: Pos) -> Span {
    // FIXME FIXME
    Span{start: p, end: p}
  }

  pub fn closure(&self, rhs: &Span) -> Span {
    let start = min(self.start, rhs.start);
    let end = max(self.end, rhs.end);
    Span{start, end}
  }
}

#[derive(Clone, Debug)]
pub enum Token {
  //NL,
  //CRNL,
  Space,
  Backslash,
  LArrow,
  Colon,
  Comma,
  Dot,
  Equals,
  Plus,
  Dash,
  Star,
  Slash,
  LParen,
  RParen,
  LBrack,
  RBrack,
  LCurly,
  RCurly,
  Def,
  Entry,
  Let,
  In,
  // TODO TODO
  F64,
  F32,
  F16,
  Bf16,
  I64,
  I32,
  I16,
  I8,
  U64,
  U32,
  U16,
  U8,
  Ident(SmolStr),
  Float(SmolStr),
  Int(SmolStr),
  _Eof,
}

impl Token {
  pub fn is_eof(&self) -> bool {
    match self {
      &Token::_Eof => true,
      _ => false
    }
  }

  pub fn is_space(&self) -> bool {
    match self {
      //&Token::NL |
      //&Token::CRNL |
      &Token::Space => true,
      _ => false
    }
  }

  pub fn is_primitive_type(&self) -> bool {
    match self {
      &Token::F64 |
      &Token::F32 |
      &Token::F16 |
      &Token::Bf16 |
      &Token::I64 |
      &Token::I32 |
      &Token::I16 |
      &Token::I8  |
      &Token::U64 |
      &Token::U32 |
      &Token::U16 |
      &Token::U8 => true,
      _ => false
    }
  }
}

pub fn tokenizer_trie() -> ReTrie<Token> {
  fn _re(s: &str) -> ReExp {
    match ReParser::new().parse(s) {
      Err(_) => panic!("bug: regexp parse failure: '{}'", s),
      Ok(rexp) => rexp
    }
  }
  let mut tr = ReTrie::default();
  //tr.push(_re(r"\n"),     |_| Token::NL);
  //tr.push(_re(r"\r\n"),   |_| Token::CRNL);
  tr.push(_re(r"[ \t\r\n]+"), |_| Token::Space);
  tr.push(_re(r"\\"),     |_| Token::Backslash);
  tr.push(_re(r"\->"),    |_| Token::LArrow);
  tr.push(_re(r"\-"),     |_| Token::Dash);
  tr.push(_re(r":"),      |_| Token::Colon);
  tr.push(_re(r","),      |_| Token::Comma);
  tr.push(_re(r"\."),     |_| Token::Dot);
  tr.push(_re(r"="),      |_| Token::Equals);
  //tr.push(_re(r"\+\+"),   |_| Token::PlusPlus);
  tr.push(_re(r"\+"),     |_| Token::Plus);
  //tr.push(_re(r"\*\*"),   |_| Token::StarStar);
  tr.push(_re(r"\*"),     |_| Token::Star);
  tr.push(_re(r"/"),      |_| Token::Slash);
  tr.push(_re(r"\("),     |_| Token::LParen);
  tr.push(_re(r"\)"),     |_| Token::RParen);
  tr.push(_re(r"\["),     |_| Token::LBrack);
  tr.push(_re(r"\]"),     |_| Token::RBrack);
  tr.push(_re(r"\{"),     |_| Token::LCurly);
  tr.push(_re(r"\}"),     |_| Token::RCurly);
  tr.push(_re(r"def"),    |_| Token::Def);
  tr.push(_re(r"entry"),  |_| Token::Entry);
  tr.push(_re(r"let"),    |_| Token::Let);
  tr.push(_re(r"in"),     |_| Token::In);
  tr.push(_re(r"f64"),    |_| Token::F64);
  tr.push(_re(r"f32"),    |_| Token::F32);
  tr.push(_re(r"f16"),    |_| Token::F16);
  tr.push(_re(r"bf16"),   |_| Token::Bf16);
  tr.push(_re(r"i64"),    |_| Token::I64);
  tr.push(_re(r"i32"),    |_| Token::I32);
  tr.push(_re(r"i16"),    |_| Token::I16);
  tr.push(_re(r"i8"),     |_| Token::I8);
  tr.push(_re(r"u64"),    |_| Token::U64);
  tr.push(_re(r"u32"),    |_| Token::U32);
  tr.push(_re(r"u16"),    |_| Token::U16);
  tr.push(_re(r"u8"),     |_| Token::U8);
  tr.push(_re(r"[a-zA-Z][a-zA-Z0-9_]*"), |s| Token::Ident(s.into()));
  tr.push(_re(r"[0-9]+\.[0-9]*"), |s| Token::Float(s.into()));
  tr.push(_re(r"[0-9]+"), |s| Token::Int(s.into()));
  tr
}

#[derive(Clone)]
pub struct Tokenizer<'t, 's> {
  trie: &'t ReTrie<Token>,
  source: &'s str,
  off: usize,
  pos: Pos,
  eof: bool,
}

impl<'t, 's> Tokenizer<'t, 's> {
  pub fn new(trie: &'t ReTrie<Token>, source: &'s str) -> Tokenizer<'t, 's> {
    Tokenizer{trie, source, off: 0, pos: Pos{line: 0, col: 0}, eof: false}
  }
}

impl<'t, 's> Iterator for Tokenizer<'t, 's> {
  type Item = (Result<Token, ()>, Span);

  fn next(&mut self) -> Option<(Result<Token, ()>, Span)> {
    if self.eof {
      return Some((Ok(Token::_Eof), Span::point(self.pos)));
    }
    let start = self.pos;
    let tok = match self.trie.match_at(self.source, self.off) {
      None => {
        self.eof = true;
        return Some((Ok(Token::_Eof), Span::point(self.pos)));
      }
      Some((tok, next_off)) => {
        let tok_len = next_off - self.off;
        self.off = next_off;
        // FIXME FIXME
        self.pos.col += tok_len;
        tok
      }
    };
    let end = self.pos;
    // FIXME FIXME
    Some((Ok(tok), Span{start, end}))
  }
}

#[derive(Clone, Debug)]
pub enum Error {
  // TODO
  Eof,
  Tok,
  UnexpectedSpace,
  Unexpected(Token),
  ExpectedSpace(Token),
  ExpectedIdent(Token),
  Expected(Token, Token),
  ExpectedAny(Vec<Token>, Token),
}

pub type ExpRef = Rc<Exp>;

#[derive(Clone, Debug)]
pub enum Exp {
  // TODO
  Lam(Vec<SmolStr>, ExpRef),
  Neg(ExpRef),
  Add(ExpRef, ExpRef),
  Sub(ExpRef, ExpRef),
  Mul(ExpRef, ExpRef),
  Div(ExpRef, ExpRef),
  App(ExpRef, ExpRef),
  //Def(SmolStr, /*...,*/ ExpRef),
  //Entry(SmolStr, /*...,*/ ExpRef),
  Let(SmolStr, ExpRef, ExpRef),
  Var(SmolStr),
}

#[derive(Clone)]
pub struct ExpParser<'t, 's> {
  tokens: Peekable<Tokenizer<'t, 's>>,
  cur: Option<(Token, Span)>,
}

impl<'t, 's> ExpParser<'t, 's> {
  pub fn new(tokens: Tokenizer<'t, 's>) -> ExpParser<'t, 's> {
    let tokens = tokens.peekable();
    ExpParser{tokens, cur: None}
  }

  pub fn next(&mut self) -> Result<(), (Error, Span)> {
    self.cur = match self.tokens.next() {
      None => None,
      Some((Ok(tok), span)) => Some((tok, span)),
      Some((Err(_), span)) => return Err((Error::Tok, span))
    };
    Ok(())
  }

  pub fn peek_next(&mut self) -> Option<&Token> {
    self.tokens.peek().and_then(|&(ref maybe_tok, _)| maybe_tok.as_ref().ok())
  }

  pub fn peek_next_(&mut self) -> (Token, Span) {
  //pub fn peek_next_(&mut self) -> Result<(Token, Span), (Error, Span)> {}
    // FIXME FIXME
    match self.tokens.peek().and_then(|&(ref maybe_tok, span)| maybe_tok.as_ref().ok().map(|t| (t.clone(), span)))
    {
      Some(x) => x,
      None => (Token::_Eof, Span::default())
      //None => Err((Error::Eof, Span::default()))
    }
  }

  /*pub fn current(&self) -> Option<(&Token, Span)> {
    self.cur.as_ref().map(|&(ref tok, span)| (tok, span))
  }*/

  pub fn current(&self) -> Token {
    self.current_().0
  }

  pub fn current_ref(&self) -> &Token {
    self.cur.as_ref().map(|&(ref tok, _)| tok).unwrap()
  }

  pub fn current_span(&self) -> Span {
    self.cur.as_ref().unwrap().1
  }

  pub fn current_(&self) -> (Token, Span) {
    self.cur.as_ref().unwrap().clone()
  }

  pub fn lbp(&self, tok: &Token) -> i16 {
    match tok {
      &Token::Plus | &Token::Dash => 500,
      &Token::Star | &Token::Slash => 550,
      &Token::LParen | &Token::LBrack | &Token::LCurly => 900,
      &Token::Space => 9999,
      _ => 0
    }
  }

  /*pub fn rbp(&self, tok: &Token) -> i16 {
    let lbp = self.lbp(tok);
    match tok {
      &Token::Star | &Token::Slash => lbp - 1,
      _ => lbp
    }
  }*/

  pub fn maybe_skip_space(&mut self) -> Result<bool, (Error, Span)> {
    match self.current_ref() {
      //&Token::NL | &Token::CRNL |
      &Token::Space => {}
      _ => return Ok(false)
    }
    loop {
      match self.peek_next() {
        //Some(&Token::NL) | Some(&Token::CRNL) |
        Some(&Token::Space) => {
          self.next()?;
          match self.current_ref() {
            //&Token::NL | &Token::CRNL | &Token::Space => {}
            &Token::Space => {}
            _ => unreachable!()
          }
        }
        _ => return Ok(true)
      }
    }
  }

  pub fn skip_space(&mut self) -> Result<(), (Error, Span)> {
    match self.current() {
      //Token::NL | Token::CRNL |
      Token::Space => {}
      t => return Err((Error::ExpectedSpace(t), self.current_span()))
    }
    loop {
      match self.peek_next() {
        //Some(&Token::NL) | Some(&Token::CRNL) |
        Some(&Token::Space) => {
          self.next()?;
          match self.current_ref() {
            //&Token::NL | &Token::CRNL |
            &Token::Space => {}
            _ => unreachable!()
          }
        }
        _ => return Ok(())
      }
    }
  }

  pub fn led(&mut self, lexp: Exp, tok: Token, span: Span, prespace: bool) -> Result<Exp, (Error, Span)> {
    match tok {
      // TODO TODO
      Token::Plus => {
        let rexp = self.exp(self.lbp(&tok))?;
        Ok(Exp::Add(lexp.into(), rexp.into()))
      }
      Token::Dash => {
        let rexp = self.exp(self.lbp(&tok))?;
        Ok(Exp::Sub(lexp.into(), rexp.into()))
      }
      Token::Star => {
        let rexp = self.exp(self.lbp(&tok))?;
        Ok(Exp::Mul(lexp.into(), rexp.into()))
      }
      Token::Slash => {
        let rexp = self.exp(self.lbp(&tok))?;
        Ok(Exp::Div(lexp.into(), rexp.into()))
      }
      Token::LBrack => {
        if prespace {
          let arg = self.nud(tok, span)?;
          Ok(Exp::App(lexp.into(), arg.into()))
        } else {
          unimplemented!();
        }
      }
      _ => panic!("bug: led: unimplemented: lexp={:?} tok={:?} span={:?}", lexp, tok, span)
    }
  }

  pub fn nud(&mut self, tok: Token, span: Span) -> Result<Exp, (Error, Span)> {
    match tok {
      Token::Space => {
        Err((Error::UnexpectedSpace, span))
      }
      Token::In => {
        Err((Error::Unexpected(tok), span))
      }
      // TODO TODO
      Token::Backslash => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let mut vars = Vec::new();
        loop {
          match self.current() {
            Token::Ident(var) => {
              vars.push(var);
            }
            t => return Err((Error::ExpectedIdent(t), self.current_span()))
          }
          self.next()?;
          if self.maybe_skip_space()? {
            self.next()?;
          }
          match self.current() {
            Token::LArrow => break,
            Token::Comma => {}
            // FIXME
            t => return Err((Error::ExpectedAny(vec![Token::LArrow, Token::Comma], t), self.current_span()))
          }
          self.next()?;
          if self.maybe_skip_space()? {
            self.next()?;
          }
        }
        self.next()?;
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let body = self.exp(0)?;
        Ok(Exp::Lam(vars, body.into()))
      }
      Token::Dash => {
        let body = self.exp(0)?;
        Ok(Exp::Neg(body.into()))
      }
      Token::Let => {
        self.skip_space()?;
        println!("TRACE: nud: Let: skip space");
        self.next()?;
        println!("TRACE: nud: Let:   next tok={:?}", self.current_ref());
        let name = match self.current() {
          Token::Ident(name) => name,
          t => return Err((Error::ExpectedIdent(t), self.current_span()))
        };
        println!("TRACE: nud: Let: name={:?}", name);
        self.next()?;
        println!("TRACE: nud: Let:   next tok={:?}", self.current_ref());
        self.skip_space()?;
        println!("TRACE: nud: Let: skip space");
        self.next()?;
        println!("TRACE: nud: Let:   next tok={:?}", self.current_ref());
        match self.current() {
          Token::Equals => {}
          t => return Err((Error::Expected(Token::Equals, t), self.current_span()))
        }
        println!("TRACE: nud: Let: =");
        self.next()?;
        println!("TRACE: nud: Let:   next tok={:?}", self.current_ref());
        self.skip_space()?;
        println!("TRACE: nud: Let: skip space");
        self.next()?;
        println!("TRACE: nud: Let:   next tok={:?}", self.current_ref());
        let body = self.exp(0)?;
        println!("TRACE: nud: Let: body={:?}", body);
        self.skip_space()?;
        println!("TRACE: nud: Let: skip space");
        self.next()?;
        match self.current() {
          Token::In => {}
          t => return Err((Error::Expected(Token::In, t), self.current_span()))
        }
        println!("TRACE: nud: Let: in");
        self.next()?;
        println!("TRACE: nud: Let:   next tok={:?}", self.current_ref());
        self.skip_space()?;
        println!("TRACE: nud: Let: skip space");
        self.next()?;
        println!("TRACE: nud: Let:   next tok={:?}", self.current_ref());
        let rest = self.exp(0)?;
        println!("TRACE: nud: Let: rest={:?}", rest);
        Ok(Exp::Let(name, body.into(), rest.into()))
      }
      Token::Ident(name) => {
        Ok(Exp::Var(name))
      }
      _ => panic!("bug: nud: unimplemented: tok={:?} span={:?}", tok, span)
    }
  }

  pub fn exp(&mut self, rbp: i16) -> Result<Exp, (Error, Span)> {
    self.exp_(rbp, false)
  }

  pub fn exp_(&mut self, rbp: i16, rec: bool) -> Result<Exp, (Error, Span)> {
    let mut tok_span = self.current_();
    println!("TRACE: exp: tok={:?} span={:?} rbp={}", tok_span.0, tok_span.1, rbp);
    if tok_span.0.is_eof() {
      return Err((Error::Eof, tok_span.1));
    }
    self.next()?;
    println!("TRACE: exp:   next tok={:?}", self.current_ref());
    let mut lexp = self.nud(tok_span.0, tok_span.1)?;
    println!("TRACE: exp:   lexp={:?}", lexp);
    tok_span = self.current_();
    println!("TRACE: exp:   tok={:?} span={:?}", tok_span.0, tok_span.1);
    if tok_span.0.is_eof() {
      println!("TRACE: exp:   return {:?}", lexp);
      return Ok(lexp);
    }
    /*while rbp < self.lbp(&tok_span.0) {
      self.next()?;
      lexp = self.led(lexp, tok_span.0, tok_span.1)?;
      tok_span = self.current_();
      if tok_span.0.is_eof() {
        return Ok(lexp);
      }
    }*/
    loop {
      let mut lbp = self.lbp(&tok_span.0);
      println!("TRACE: exp:   tok={:?}", &tok_span.0);
      println!("TRACE: exp:   lbp={}", lbp);
      let mut prespace = false;
      if tok_span.0.is_space() {
        //self.next()?;
        //tok_span = self.current_();
        tok_span = self.peek_next_();
        assert!(!tok_span.0.is_space());
        if tok_span.0.is_eof() {
          println!("TRACE: exp:   return {:?}", lexp);
          return Ok(lexp);
        }
        lbp = self.lbp(&tok_span.0);
        prespace = true;
        println!("TRACE: exp:   lbp={} (prespace)", lbp);
      }
      if rbp < lbp {
        if prespace {
          self.next()?;
          println!("TRACE: exp:   next tok={:?} (prespace)", self.current_ref());
        }
        self.next()?;
        println!("TRACE: exp:   next tok={:?}", self.current_ref());
        lexp = self.led(lexp, tok_span.0, tok_span.1, prespace)?;
        println!("TRACE: exp:   lexp={:?}", lexp);
        tok_span = self.current_();
        if tok_span.0.is_eof() {
          println!("TRACE: exp:   return {:?}", &lexp);
          return Ok(lexp);
        }
      } else if !rec {
        println!("TRACE: exp:   backtrack: enter...");
        let mut parser = self.clone();
        println!("TRACE: exp:   backtrack: tok={:?}", &tok_span.0);
        println!("TRACE: exp:   backtrack: prespace?{:?}", prespace);
        println!("TRACE: exp:   backtrack: cur={:?}", parser.current_ref());
        println!("TRACE: exp:   backtrack: next={:?}", parser.peek_next());
        if prespace || parser.current_ref().is_space() {
          parser.next()?;
          println!("TRACE: exp:   backtrack: next tok={:?} (prespace)", parser.current_ref());
        }
        //parser.next()?;
        //println!("TRACE: exp:   backtrack: next tok={:?}", parser.current_ref());
        // FIXME: following might prefer `exp(rbp)`; think about this.
        match parser.exp_(0, true) {
          Ok(arg) => {
            *self = parser;
            println!("TRACE: exp:   backtrack: return {:?}", arg);
            //return Ok(Exp::App(lexp.into(), arg.into()));
            lexp = Exp::App(lexp.into(), arg.into());
            println!("TRACE: exp:   lexp={:?}", &lexp);
          }
          Err(_) => {
            println!("TRACE: exp:   backtrack: failed");
            break;
          }
        }
      } else {
        break;
      }
    }
    println!("TRACE: exp:   return {:?}", lexp);
    Ok(lexp)
  }

  pub fn parse(mut self) -> Result<Exp, (Error, Span)> {
    self.next()?;
    self.exp(0)
  }
}
