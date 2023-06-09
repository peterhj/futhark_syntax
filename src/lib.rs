extern crate regex_syntax;
extern crate smol_str;

use crate::re::{ReTrie};

//use regex_syntax::{Parser as ReParser};
//use regex_syntax::hir::{Hir as ReExp};
use smol_str::{SmolStr};

use std::cmp::{Ordering, max, min};
use std::iter::{Peekable};
use std::rc::{Rc};

pub mod re;
#[cfg(test)] pub mod tests;

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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum FloatLitKind {
  Dec,
  Exp,
  Hex,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum IntLitKind {
  Dec,
  Hex,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Token {
  Space,
  NL,
  CRNL,
  Backslash,
  LArrow,
  Comma,
  Colon,
  ColonGt,
  Dot,
  DotDot,
  DotDotDot,
  DotDotGt,
  DotDotLt,
  Equals,
  EqEq,
  Neq,
  Gt,
  GtEq,
  GtGt,
  Lt,
  LtEq,
  LtLt,
  Plus,
  Dash,
  Star,
  Slash,
  DSlash,
  Percent,
  DPercent,
  Amp,
  AmpAmp,
  VBar,
  VBarBar,
  Caret,
  Bang,
  Hash,
  //Backtick,
  //DQuote,
  LPipe,
  RPipe,
  LRParen,
  LParen,
  RParen,
  LHashBrack,
  LRBrack,
  LBrack,
  RBrack,
  LRCurly,
  LCurly,
  RCurly,
  Def,
  Entry,
  Let,
  In,
  If,
  Then,
  Else,
  Loop,
  Do,
  Match,
  Case,
  With,
  Unsafe,
  Assert,
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
  Bool,
  False,
  True,
  Underscore,
  Ident(SmolStr),
  InfixIdent(SmolStr),
  FloatLit(SmolStr, FloatLitKind),
  IntLit(SmolStr, IntLitKind),
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
      &Token::NL | &Token::CRNL |
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

  pub fn expected_ident(self, span: Span) -> Result<SmolStr, (ExpError, Span)> {
    match self {
      Token::Ident(name) => Ok(name),
      s => Err((ExpError::ExpectedIdent(s), span))
    }
  }

  pub fn expected(self, t: Token, span: Span) -> Result<(), (ExpError, Span)> {
    if self != t {
      return Err((ExpError::Expected(t, self), span));
    }
    Ok(())
  }
}

pub fn tokenizer_trie() -> ReTrie<Token> {
  let mut tr = ReTrie::default();
  /*tr.push(r"[ \t\r\n]+", |_| Token::Space);*/
  tr.push(r"\r\n",      |_| Token::CRNL);
  tr.push(r"\n",        |_| Token::NL);
  tr.push(r"[ \t]+",    |_| Token::Space);
  tr.push(r"\\",        |_| Token::Backslash);
  tr.push(r"\->",       |_| Token::LArrow);
  tr.push(r"\-",        |_| Token::Dash);
  tr.push(r":>",        |_| Token::ColonGt);
  tr.push(r":",         |_| Token::Colon);
  tr.push(r",",         |_| Token::Comma);
  tr.push(r"==",        |_| Token::EqEq);
  tr.push(r"=",         |_| Token::Equals);
  tr.push(r">=",        |_| Token::GtEq);
  tr.push(r">>",        |_| Token::GtGt);
  tr.push(r">",         |_| Token::Gt);
  tr.push(r"<\|",       |_| Token::LPipe);
  tr.push(r"<=",        |_| Token::LtEq);
  tr.push(r"<<",        |_| Token::LtLt);
  tr.push(r"<",         |_| Token::Lt);
  //tr.push(r"\+\+",      |_| Token::PlusPlus);
  tr.push(r"\+",        |_| Token::Plus);
  //tr.push(r"\*\*",      |_| Token::StarStar);
  tr.push(r"\*",        |_| Token::Star);
  tr.push(r"//",        |_| Token::DSlash);
  tr.push(r"/",         |_| Token::Slash);
  tr.push(r"%%",        |_| Token::DPercent);
  tr.push(r"%",         |_| Token::Percent);
  tr.push(r"!=",        |_| Token::Neq);
  tr.push(r"!",         |_| Token::Bang);
  tr.push(r"&&",        |_| Token::AmpAmp);
  tr.push(r"&",         |_| Token::Amp);
  tr.push(r"\|>",       |_| Token::RPipe);
  tr.push(r"\|\|",      |_| Token::VBarBar);
  tr.push(r"\|",        |_| Token::VBar);
  tr.push(r"\^",        |_| Token::Caret);
  tr.push(r"#\[",       |_| Token::LHashBrack);
  tr.push(r"#",         |_| Token::Hash);
  tr.push(r"\(\)",      |_| Token::LRParen);
  tr.push(r"\(",        |_| Token::LParen);
  tr.push(r"\)",        |_| Token::RParen);
  tr.push(r"\[\]",      |_| Token::LRBrack);
  tr.push(r"\[",        |_| Token::LBrack);
  tr.push(r"\]",        |_| Token::RBrack);
  tr.push(r"\{\}",      |_| Token::LRCurly);
  tr.push(r"\{",        |_| Token::LCurly);
  tr.push(r"\}",        |_| Token::RCurly);
  tr.push(r"def",       |_| Token::Def);
  tr.push(r"entry",     |_| Token::Entry);
  tr.push(r"let",       |_| Token::Let);
  tr.push(r"in",        |_| Token::In);
  tr.push(r"if",        |_| Token::If);
  tr.push(r"then",      |_| Token::Then);
  tr.push(r"else",      |_| Token::Else);
  tr.push(r"loop",      |_| Token::Loop);
  tr.push(r"do",        |_| Token::Do);
  tr.push(r"match",     |_| Token::Match);
  tr.push(r"case",      |_| Token::Case);
  tr.push(r"with",      |_| Token::With);
  tr.push(r"unsafe",    |_| Token::Unsafe);
  tr.push(r"assert",    |_| Token::Assert);
  tr.push(r"f64",       |_| Token::F64);
  tr.push(r"f32",       |_| Token::F32);
  tr.push(r"f16",       |_| Token::F16);
  tr.push(r"bf16",      |_| Token::Bf16);
  tr.push(r"i64",       |_| Token::I64);
  tr.push(r"i32",       |_| Token::I32);
  tr.push(r"i16",       |_| Token::I16);
  tr.push(r"i8",        |_| Token::I8);
  tr.push(r"u64",       |_| Token::U64);
  tr.push(r"u32",       |_| Token::U32);
  tr.push(r"u16",       |_| Token::U16);
  tr.push(r"u8",        |_| Token::U8);
  tr.push(r"bool",      |_| Token::Bool);
  tr.push(r"false",     |_| Token::False);
  tr.push(r"true",      |_| Token::True);
  tr.push(r"_",         |_| Token::Underscore);
  tr.push(r"`[a-zA-Z_][a-zA-Z0-9_]*`",
                        |s| Token::InfixIdent(s.into()));
  tr.push(r"[a-zA-Z_][a-zA-Z0-9_]*",
                        |s| Token::Ident(s.into()));
  tr.push(r"0[xX][0-9a-fA-F][0-9a-fA-F_]*\.[0-9a-fA-F][0-9a-fA-F_]*[pP][\+\-]+[0-9][0-9]*",
                        |s| Token::FloatLit(s.into(), FloatLitKind::Hex));
  tr.push(r"0[xX][0-9a-fA-F][0-9a-fA-F_]*",
                        |s| Token::IntLit(s.into(), IntLitKind::Hex));
  tr.push(r"[0-9][0-9_]*\.[0-9][0-9_]*[eE][\+\-]+[0-9][0-9]*",
                        |s| Token::FloatLit(s.into(), FloatLitKind::Exp));
  tr.push(r"[0-9][0-9_]*\.[0-9][0-9_]*",
                        |s| Token::FloatLit(s.into(), FloatLitKind::Dec));
  tr.push(r"[0-9][0-9_]*[eE][\+\-]+[0-9][0-9]*",
                        |s| Token::FloatLit(s.into(), FloatLitKind::Exp));
  tr.push(r"[0-9][0-9_]*",
                        |s| Token::IntLit(s.into(), IntLitKind::Dec));
  //tr.push(r"`",         |_| Token::Backtick);
  //tr.push(r"\"",        |_| Token::DQuote);
  tr.push(r"\.\.<",     |_| Token::DotDotLt);
  tr.push(r"\.\.>",     |_| Token::DotDotGt);
  tr.push(r"\.\.\.",    |_| Token::DotDotDot);
  tr.push(r"\.\.",      |_| Token::DotDot);
  tr.push(r"\.",        |_| Token::Dot);
  tr
}

#[derive(Clone)]
pub struct Tokenizer<'t, 's> {
  trie: &'t ReTrie<Token>,
  source: &'s str,
  off: usize,
  pos: Pos,
  eof: bool,
  peek: Option<(Token, usize)>,
}

impl<'t, 's> Tokenizer<'t, 's> {
  pub fn new(trie: &'t ReTrie<Token>, source: &'s str) -> Tokenizer<'t, 's> {
    Tokenizer{trie, source, off: 0, pos: Pos{line: 0, col: 0}, eof: false, peek: None}
  }
}

impl<'t, 's> Iterator for Tokenizer<'t, 's> {
  //type Item = (Result<Token, ()>, Span);
  type Item = (Token, Span);

  //fn next(&mut self) -> Option<(Result<Token, ()>, Span)> {}
  fn next(&mut self) -> Option<(Token, Span)> {
    if let Some((next_tok, next_off)) = self.peek.take() {
      let start = self.pos;
      let tok_len = next_off - self.off;
      self.off = next_off;
      // FIXME: calculate pos.
      self.pos.col += tok_len;
      let end = self.pos;
      return Some((next_tok, Span{start, end}));
    }
    if self.eof {
      //return Some((Ok(Token::_Eof), Span::point(self.pos)));
      return Some((Token::_Eof, Span::point(self.pos)));
    }
    let start = self.pos;
    let mut tok = match self.trie.match_at(self.source, self.off) {
      None => {
        self.eof = true;
        //return Some((Ok(Token::_Eof), Span::point(self.pos)));
        return Some((Token::_Eof, Span::point(self.pos)));
      }
      Some((next_tok, next_off)) => {
        let tok_len = next_off - self.off;
        self.off = next_off;
        // FIXME: calculate pos.
        self.pos.col += tok_len;
        next_tok
      }
    };
    if tok.is_space() {
      tok = Token::Space;
      loop {
        match self.trie.match_at(self.source, self.off) {
          None => {
            self.eof = true;
            break;
          }
          Some((next_tok, next_off)) => {
            if !next_tok.is_space() {
              self.peek = Some((next_tok, next_off));
              break;
            }
            let tok_len = next_off - self.off;
            self.off = next_off;
            // FIXME: calculate pos.
            self.pos.col += tok_len;
          }
        }
      }
    }
    let end = self.pos;
    //Some((Ok(tok), Span{start, end}))
    Some((tok, Span{start, end}))
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExpError {
  // TODO
  Eof,
  Tok,
  Failed(Token),
  UnexpectedSpace,
  Unexpected(Token),
  ExpectedSpace(Token),
  ExpectedIdent(Token),
  Expected(Token, Token),
  ExpectedAny(Vec<Token>, Token),
}

impl ExpError {
  pub fn is_eof(&self) -> bool {
    match self {
      &ExpError::Eof => true,
      _ => false
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum FloatType {
  F64,
  F32,
  F16,
  Bf16,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum IntType {
  I64,
  I32,
  I16,
  I8,
  U64,
  U32,
  U16,
  U8,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PrimType {
  Float(FloatType),
  Int(IntType),
  Bool,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum InfixOp {
  Add,
  Sub,
  Mul,
  Div,
  Rem,
  Id(SmolStr),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PrefixOp {
  Neg,
  BNeg,
}

pub type TypeExpRef = Rc<TypeExp>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TypeExp {
  // TODO
  Prim(PrimType),
}

pub type ExpRef = Rc<Exp>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Exp {
  // TODO
  Lam(Vec<SmolStr>, ExpRef),
  LamAlt(Vec<SmolStr>, ExpRef),
  //LamTy(Vec<SmolStr>, Option<TypeExpRef>, ExpRef),
  //LamAltTy(Vec<SmolStr>, Option<TypeExpRef>, ExpRef),
  App(ExpRef, ExpRef),
  InfixApp(InfixOp, ExpRef, ExpRef),
  Add(ExpRef, ExpRef),
  Sub(ExpRef, ExpRef),
  Mul(ExpRef, ExpRef),
  Div(ExpRef, ExpRef),
  Rem(ExpRef, ExpRef),
  Neg(ExpRef),
  //Def(SmolStr, /*...,*/ ExpRef),
  //Entry(SmolStr, /*...,*/ ExpRef),
  Let(SmolStr, ExpRef, ExpRef),
  FloatLit(SmolStr, FloatLitKind, Option<FloatType>),
  IntLit(SmolStr, IntLitKind, Option<IntType>),
  InfixOp(InfixOp),
  PrefixOp(PrefixOp),
  Id(SmolStr),
}

impl Exp {
  pub fn id<S: AsRef<str>>(s: S) -> Exp {
    Exp::Id(s.as_ref().into())
  }
}

#[derive(Clone)]
pub struct ExpParser<'t, 's> {
  tokens: Peekable<Tokenizer<'t, 's>>,
  cur: Option<(Token, Span)>,
  trace: bool,
  //depth: u32,
}

impl<'t, 's> ExpParser<'t, 's> {
  pub fn new(tokens: Tokenizer<'t, 's>) -> ExpParser<'t, 's> {
    let tokens = tokens.peekable();
    ExpParser{tokens, cur: None, trace: false, /*depth: 0*/}
  }

  pub fn next(&mut self) -> Result<(), (ExpError, Span)> {
    self.cur = match self.tokens.next() {
      //None => None,
      None => unreachable!(),
      //Some((Ok(tok), span)) => Some((tok, span)),
      //Some((Err(_), span)) => return Err((ExpError::Tok, span))
      Some((tok, span)) => Some((tok, span))
    };
    Ok(())
  }

  pub fn peek_next(&mut self) -> Option<&Token> {
    //self.tokens.peek().and_then(|&(ref maybe_tok, _)| maybe_tok.as_ref().ok())
    self.tokens.peek().map(|&(ref tok, _)| tok)
  }

  pub fn peek_next_(&mut self) -> (Token, Span) {
  //pub fn peek_next_(&mut self) -> Result<(Token, Span), (ExpError, Span)> {}
    // FIXME FIXME
    //match self.tokens.peek().and_then(|&(ref maybe_tok, span)| maybe_tok.as_ref().ok().map(|t| (t.clone(), span)))
    match self.tokens.peek().map(|&(ref tok, span)| (tok.clone(), span))
    {
      //None => Err((ExpError::Eof, Span::default()))
      None => (Token::_Eof, Span::default()),
      Some((tok, span)) => (tok, span)
    }
  }

  /*pub fn current(&self) -> Option<(&Token, Span)> {
    self.cur.as_ref().map(|&(ref tok, span)| (tok, span))
  }*/

  pub fn current(&self) -> Token {
    //self.current_().0
    (self.cur.as_ref().unwrap().0).clone()
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
      &Token::InfixIdent(_) => 500,
      &Token::VBarBar => 510,
      &Token::AmpAmp => 520,
      &Token::EqEq |
      &Token::Neq |
      &Token::Gt |
      &Token::GtEq |
      &Token::Lt |
      &Token::LtEq => 525,
      &Token::Amp |
      &Token::VBar |
      &Token::Caret => 530,
      &Token::GtGt |
      &Token::LtLt => 540,
      &Token::Plus |
      &Token::Dash => 550,
      &Token::Star |
      &Token::Slash |
      &Token::Percent => 575,
      &Token::LParen |
      &Token::LBrack |
      &Token::LCurly => 900,
      &Token::Space => 9999,
      _ => 0
    }
  }

  pub fn maybe_skip_space(&mut self) -> Result<bool, (ExpError, Span)> {
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

  pub fn skip_space(&mut self) -> Result<(), (ExpError, Span)> {
    match self.current() {
      //Token::NL | Token::CRNL |
      Token::Space => {}
      t => return Err((ExpError::ExpectedSpace(t), self.current_span()))
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

  pub fn led(&mut self, lexp: Exp, tok: Token, span: Span, /*prespace: bool*/) -> Result<Exp, (ExpError, Span)> {
    let lbp = self.lbp(&tok);
    match tok {
      Token::LRParen |
      Token::LParen |
      Token::RParen |
      Token::LRBrack |
      Token::RBrack |
      Token::LRCurly |
      Token::LCurly |
      Token::RCurly => {
        Err((ExpError::Unexpected(tok), span))
      }
      // TODO TODO
      Token::Plus => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let rexp = self.exp(lbp)?;
        Ok(Exp::Add(lexp.into(), rexp.into()))
      }
      Token::Dash => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let rexp = self.exp(lbp)?;
        Ok(Exp::Sub(lexp.into(), rexp.into()))
      }
      Token::Star => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let rexp = self.exp(lbp)?;
        Ok(Exp::Mul(lexp.into(), rexp.into()))
      }
      Token::Slash => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let rexp = self.exp(lbp)?;
        Ok(Exp::Div(lexp.into(), rexp.into()))
      }
      Token::Percent => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let rexp = self.exp(lbp)?;
        Ok(Exp::Rem(lexp.into(), rexp.into()))
      }
      Token::LBrack => {
        unimplemented!();
      }
      Token::InfixIdent(name) => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let rexp = self.exp(lbp)?;
        Ok(Exp::InfixApp(InfixOp::Id(name), lexp.into(), rexp.into()))
      }
      _ => panic!("bug: led: unimplemented: lexp={:?} tok={:?} span={:?}", lexp, tok, span)
    }
  }

  pub fn nud(&mut self, tok: Token, span: Span) -> Result<Exp, (ExpError, Span)> {
    match tok {
      Token::Space => {
        Err((ExpError::UnexpectedSpace, span))
      }
      Token::In |
      Token::Plus |
      Token::Star |
      Token::Slash |
      Token::Percent |
      Token::InfixIdent(_) |
      Token::RParen |
      Token::RBrack |
      Token::RCurly => {
        Err((ExpError::Unexpected(tok), span))
      }
      // TODO TODO
      Token::Backslash => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let mut vars = Vec::new();
        loop {
          let var = self.current().expected_ident(self.current_span())?;
          vars.push(var);
          self.next()?;
          if self.maybe_skip_space()? {
            self.next()?;
          }
          match self.current() {
            Token::LArrow => break,
            // FIXME FIXME: no comma.
            Token::Comma => {}
            t => return Err((ExpError::ExpectedAny(vec![Token::LArrow, Token::Comma], t), self.current_span()))
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
        Ok(Exp::LamAlt(vars, body.into()))
      }
      Token::Dash => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let body = self.exp(9999)?;
        Ok(Exp::Neg(body.into()))
      }
      Token::LParen => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        match self.current_ref() {
          &Token::Backslash => {
            let (tok, span) = self.current_();
            self.next()?;
            let (lam_vars, lam_body) = match self.nud(tok, span)? {
              Exp::LamAlt(vars, body) => (vars, body),
              _ => return Err((ExpError::Failed(Token::Backslash), span))
            };
            if self.maybe_skip_space()? {
              self.next()?;
            }
            self.current().expected(Token::RParen, self.current_span())?;
            self.next()?;
            return Ok(Exp::Lam(lam_vars, lam_body));
          }
          &Token::Dash => {
            let (tok, span) = self.current_();
            self.next()?;
            // FIXME
            let (prespace, next_tok_span) = if self.maybe_skip_space()? {
              (true, self.peek_next_())
            } else {
              (false, self.current_())
            };
            match &next_tok_span.0 {
              Token::RParen => {
                if prespace {
                  self.next()?;
                }
                self.next()?;
                // FIXME
                return Ok(Exp::InfixOp(InfixOp::Sub));
                //return Ok(Exp::PrefixOp(PrefixOp::Neg));
              }
              _ => {}
            }
            let neg_inner = match self.nud(tok, span)? {
              Exp::Neg(inner) => inner,
              _ => return Err((ExpError::Failed(Token::Dash), span))
            };
            if self.maybe_skip_space()? {
              self.next()?;
            }
            self.current().expected(Token::RParen, self.current_span())?;
            self.next()?;
            return Ok(Exp::Neg(neg_inner));
          }
          &Token::Plus |
          &Token::Star |
          &Token::Slash |
          &Token::InfixIdent(_) => {
            if self.trace { println!("TRACE: nud: LParen: infix op..."); }
            let lexp = match self.current() {
              Token::Plus => Exp::InfixOp(InfixOp::Add),
              Token::Star => Exp::InfixOp(InfixOp::Mul),
              Token::Slash => Exp::InfixOp(InfixOp::Div),
              Token::Percent => Exp::InfixOp(InfixOp::Rem),
              Token::InfixIdent(name) => Exp::InfixOp(InfixOp::Id(name)),
              _ => unreachable!()
            };
            if self.trace { println!("TRACE: nud: LParen:   lexp={:?}", lexp); }
            self.next()?;
            let (tok, span) = self.current_();
            if self.trace { println!("TRACE: nud: LParen:   tok={:?} span={:?}", tok, span); }
            let lexp = self.exp_rec_(lexp, (tok, span), 9999, /*false*/)?;
            if self.trace { println!("TRACE: nud: LParen:   return {:?}", lexp); }
            if self.maybe_skip_space()? {
              self.next()?;
            }
            self.current().expected(Token::RParen, self.current_span())?;
            self.next()?;
            return Ok(lexp);
          }
          _ => {}
        }
        let inner = self.exp(0)?;
        if self.maybe_skip_space()? {
          self.next()?;
        }
        self.current().expected(Token::RParen, self.current_span())?;
        self.next()?;
        return Ok(inner);
      }
      Token::LBrack => {
        unimplemented!();
      }
      Token::LCurly => {
        unimplemented!();
      }
      Token::Let => {
        self.skip_space()?;
        if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        let name = self.current().expected_ident(self.current_span())?;
        if self.trace { println!("TRACE: nud: Let: name={:?}", name); }
        self.next()?;
        if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        self.skip_space()?;
        if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        self.current().expected(Token::Equals, self.current_span())?;
        if self.trace { println!("TRACE: nud: Let: ="); }
        self.next()?;
        if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        self.skip_space()?;
        if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        let body = self.exp(0)?;
        if self.trace { println!("TRACE: nud: Let: body={:?}", body); }
        self.skip_space()?;
        if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        self.current().expected(Token::In, self.current_span())?;
        if self.trace { println!("TRACE: nud: Let: in"); }
        self.next()?;
        if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        self.skip_space()?;
        if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        let rest = self.exp(0)?;
        if self.trace { println!("TRACE: nud: Let: rest={:?}", rest); }
        Ok(Exp::Let(name, body.into(), rest.into()))
      }
      Token::FloatLit(lit, kind) => {
        let mut ty = None;
        match self.current_ref() {
          &Token::F64 => ty = Some(FloatType::F64),
          &Token::F32 => ty = Some(FloatType::F32),
          &Token::F16 => ty = Some(FloatType::F16),
          &Token::Bf16 => ty = Some(FloatType::Bf16),
          _ => {}
        }
        if ty.is_some() {
          self.next()?;
        }
        Ok(Exp::FloatLit(lit, kind, ty))
      }
      Token::IntLit(lit, kind) => {
        let mut ty = None;
        match self.current_ref() {
          &Token::I64 => ty = Some(IntType::I64),
          &Token::I32 => ty = Some(IntType::I32),
          &Token::I16 => ty = Some(IntType::I16),
          &Token::I8 => ty = Some(IntType::I8),
          &Token::U64 => ty = Some(IntType::U64),
          &Token::U32 => ty = Some(IntType::U32),
          &Token::U16 => ty = Some(IntType::U16),
          &Token::U8 => ty = Some(IntType::U8),
          _ => {}
        }
        if ty.is_some() {
          self.next()?;
        }
        Ok(Exp::IntLit(lit, kind, ty))
      }
      Token::Ident(name) => {
        Ok(Exp::Id(name))
      }
      _ => panic!("bug: nud: unimplemented: tok={:?} span={:?}", tok, span)
    }
  }

  pub fn exp(&mut self, rbp: i16) -> Result<Exp, (ExpError, Span)> {
    self.exp_(rbp, false)
  }

  pub fn exp_(&mut self, rbp: i16, only_nud: bool) -> Result<Exp, (ExpError, Span)> {
    //if self.trace { self.depth += 1; }
    let mut tok_span = self.current_();
    if self.trace { println!("TRACE: exp: tok={:?} span={:?} rbp={}", tok_span.0, tok_span.1, rbp); }
    if tok_span.0.is_eof() {
      return Err((ExpError::Eof, tok_span.1));
    }
    if tok_span.0.is_space() {
      self.next()?;
      tok_span = self.current_();
    }
    if tok_span.0.is_eof() {
      return Err((ExpError::Eof, tok_span.1));
    }
    self.next()?;
    if self.trace { println!("TRACE: exp:   next tok={:?}", self.current_ref()); }
    let lexp = self.nud(tok_span.0, tok_span.1)?;
    if self.trace { println!("TRACE: exp:   lexp={:?} (nud)", lexp); }
    tok_span = self.current_();
    if self.trace { println!("TRACE: exp:   tok={:?} span={:?}", tok_span.0, tok_span.1); }
    if tok_span.0.is_eof() {
      if self.trace { println!("TRACE: exp:   return {:?}", lexp); }
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
    if !only_nud {
      return self.exp_rec_(lexp, tok_span, rbp, /*only_nud*/);
    }
    if self.trace { println!("TRACE: exp:   return {:?}", lexp); }
    Ok(lexp)
  }

  pub fn exp_rec_(&mut self, mut lexp: Exp, mut tok_span: (Token, Span), rbp: i16, /*non_rec: bool*/) -> Result<Exp, (ExpError, Span)> {
    loop {
      let mut lbp = self.lbp(&tok_span.0);
      if self.trace { println!("TRACE: exp:   tok={:?}", &tok_span.0); }
      if self.trace { println!("TRACE: exp:   lbp={}", lbp); }
      let mut prespace = false;
      let mut only_led = false;
      let mut only_rec = false;
      if tok_span.0.is_space() {
        tok_span = self.peek_next_();
        assert!(!tok_span.0.is_space());
        if tok_span.0.is_eof() {
          if self.trace { println!("TRACE: exp:   return {:?}", &lexp); }
          return Ok(lexp);
        }
        lbp = self.lbp(&tok_span.0);
        if self.trace { println!("TRACE: exp:   tok={:?} (prespace)", &tok_span.0); }
        if self.trace { println!("TRACE: exp:   lbp={} (prespace)", lbp); }
        prespace = true;
        if let &Token::LBrack = &tok_span.0 {
          only_rec = true;
        }
      }
      if let &Token::Dash = &tok_span.0 {
        only_led = true;
      }
      if only_led {
        if self.trace { println!("TRACE: exp:   only_led"); }
      }
      if only_rec {
        if self.trace { println!("TRACE: exp:   only_rec"); }
      }
      let mut mat = false;
      let mut err_led = None;
      let mut err_rec = None;
      let mut fail_led = false;
      if !only_rec && rbp < lbp {
        if self.trace { println!("TRACE: exp:   led: rbp={} < lbp={}", rbp, lbp); }
        let mut parser = self.clone();
        if prespace {
          parser.next()?;
          if self.trace { println!("TRACE: exp:   led: next tok={:?} (prespace)", self.current_ref()); }
        }
        parser.next()?;
        if self.trace { println!("TRACE: exp:   led: next tok={:?}", self.current_ref()); }
        match parser.led(lexp.clone(), tok_span.0.clone(), tok_span.1, /*prespace*/) {
          Err(e) => {
            //if self.trace { println!("TRACE: exp:   led: failed tok={:?} only_led={:?} non_rec={:?}", &tok_span.0, only_led, non_rec); }
            if self.trace { println!("TRACE: exp:   led: failed tok={:?} only_led={:?}", &tok_span.0, only_led); }
            err_led = Some(e);
            fail_led = true;
          }
          Ok(led_exp) => {
            *self = parser;
            lexp = led_exp;
            tok_span = self.current_();
            if self.trace { println!("TRACE: exp:   led: lexp={:?}", &lexp); }
            if self.trace { println!("TRACE: exp:   led: tok={:?}", &tok_span.0); }
            if tok_span.0.is_eof() {
              if self.trace { println!("TRACE: exp:   return {:?}", &lexp); }
              return Ok(lexp);
            }
            mat = true;
          }
        }
      }
      if !only_led && (fail_led || rbp >= lbp) {
        if self.trace { println!("TRACE: exp:   backtrack: enter... fail_led={:?} rbp={} lbp={}", fail_led, rbp, lbp); }
        let mut parser = self.clone();
        if self.trace { println!("TRACE: exp:   backtrack: tok={:?}", &tok_span.0); }
        if self.trace { println!("TRACE: exp:   backtrack: prespace?{:?}", prespace); }
        if self.trace { println!("TRACE: exp:   backtrack: cur={:?}", parser.current_ref()); }
        if self.trace { println!("TRACE: exp:   backtrack: peek next={:?}", parser.peek_next()); }
        if prespace {
          parser.next()?;
          if self.trace { println!("TRACE: exp:   backtrack: next tok={:?} (prespace)", parser.current_ref()); }
        }
        match parser.exp_(9999, true) {
          Err(e) => {
            err_rec = Some(e);
            if self.trace { println!("TRACE: exp:   backtrack: failed"); }
          }
          Ok(arg_exp) => {
            *self = parser;
            if self.trace { println!("TRACE: exp:   backtrack: return {:?}", &arg_exp); }
            lexp = Exp::App(lexp.into(), arg_exp.into());
            tok_span = self.current_();
            if self.trace { println!("TRACE: exp:   backtrack: lexp={:?}", &lexp); }
            if self.trace { println!("TRACE: exp:   backtrack: tok={:?}", &tok_span.0); }
            if tok_span.0.is_eof() {
              if self.trace { println!("TRACE: exp:   return {:?}", lexp); }
              return Ok(lexp);
            }
            mat = true;
          }
        }
      }
      if !mat {
        if self.trace { if err_led.is_some() || err_rec.is_some() {
          println!("TRACE: exp:   no mat and err");
          if let Some(ref e) = err_led {
            println!("TRACE: exp:     err led={:?}", e);
          }
          if let Some(ref e) = err_rec {
            println!("TRACE: exp:     err rec={:?}", e);
          }
        } }
        if err_led.as_ref()
             .map(|&(ref e, _)| e.is_eof())
             .unwrap_or(false)
           && err_rec.is_some()
        {
          return Err(err_led.unwrap());
        }
        break;
      }
    }
    if self.trace { println!("TRACE: exp:   return {:?}", lexp); }
    Ok(lexp)
  }

  pub fn trace(mut self) -> ExpParser<'t, 's> {
    self.trace = true;
    //self.depth = 0;
    self
  }

  pub fn parse(mut self) -> Result<Exp, (ExpError, Span)> {
    self.next()?;
    self.exp(0)
  }
}
