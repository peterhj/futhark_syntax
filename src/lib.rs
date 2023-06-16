extern crate regex_syntax;
extern crate smol_str;

use crate::re::{ReTrie};

use smol_str::{SmolStr};

use std::borrow::{Cow};
use std::cmp::{Ordering, max, min};
use std::iter::{Peekable};
use std::rc::{Rc};
use std::str::{from_utf8};

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
  LF,
  CRLF,
  Comment,
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
  StarStar,
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
  Dollar,
  Hash,
  Query,
  TQuery,
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
  // FIXME FIXME
  InfixOpLit(SmolStr),
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
      &Token::LF | &Token::CRLF |
      &Token::Comment |
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
  let mut tr = ReTrie::default();
  /*tr.push(r"[ \t\r\n]+", |_| Token::Space);*/
  /*tr.push(r"\-\-.*\n",  |_| Token::Comment);*/
  tr.push(r"\r\n",      |_| Token::CRLF);
  tr.push(r"\n",        |_| Token::LF);
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
  tr.push(r"\*\*",      |_| Token::StarStar);
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
  tr.push(r"\?\?\?",    |_| Token::TQuery);
  tr.push(r"\?",        |_| Token::Query);
  tr.push(r"\$",        |_| Token::Dollar);
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
pub struct Tokenizer<'s> {
  trie: Rc<ReTrie<Token>>,
  src:  Cow<'s, str>,
  off:  usize,
  pos:  Pos,
  eof:  bool,
  peek: Option<(Token, usize)>,
}

impl<'s> Tokenizer<'s> {
  pub fn new<S: Into<Cow<'s, str>>>(trie: Rc<ReTrie<Token>>, src: S) -> Tokenizer<'s> {
    let src = src.into();
    Tokenizer{trie, src, off: 0, pos: Pos{line: 0, col: 0}, eof: false, peek: None}
  }
}

impl<'s> Iterator for Tokenizer<'s> {
  type Item = (Token, Span);

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
      return Some((Token::_Eof, Span::point(self.pos)));
    }
    let start = self.pos;
    let mut tok = match self.trie.match_at(self.src.as_ref(), self.off) {
      None => {
        self.eof = true;
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
        match self.trie.match_at(self.src.as_ref(), self.off) {
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
    Some((tok, Span{start, end}))
  }
}

pub type ExpRet = Result<Exp, (ExpError, Span)>;
//pub type ExpRet = Result<(Exp, Span), (ExpError, Span)>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExpError {
  // TODO
  Eof,
  Tok,
  InvalidNud(Token),
  InvalidLed(Token),
  Failed(Token),
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

  pub fn is_invalid(&self) -> bool {
    match self {
      &ExpError::InvalidNud(_) |
      &ExpError::InvalidLed(_) => true,
      _ => false
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum ExpCtx {
  Top,
  Root,
  Parens,
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
  InfixPartL(InfixOp, ExpRef),
  InfixPartR(ExpRef, InfixOp),
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
pub struct ExpParser<'s> {
  tokens: Peekable<Tokenizer<'s>>,
  cur: Option<(Token, Span)>,
  trace: bool,
  depth: u32,
}

impl Token {
  pub fn expected_ident(self, p: &mut ExpParser) -> Result<SmolStr, (ExpError, Span)> {
    match &self {
      &Token::Ident(_) => {
        match self {
          Token::Ident(name) => Ok(name),
          _ => unreachable!()
        }
      }
      _ => {
        let span = p.current_span();
        if p._trace2("exp", "tok") { println!("expected ident, actual={:?}", &self); }
        if p.trace { p.depth -= 1; }
        let s = match self {
          Token::Ident(_) => unreachable!(),
          s => s
        };
        Err((ExpError::ExpectedIdent(s), span))
      }
    }
  }

  pub fn expected(self, t: Token, p: &mut ExpParser) -> Result<(), (ExpError, Span)> {
    if &self != &t {
      let span = p.current_span();
      if p._trace2("exp", "tok") { println!("expected={:?}, actual={:?}", &t, &self); }
      if p.trace { p.depth -= 1; }
      return Err((ExpError::Expected(t, self), span));
    }
    Ok(())
  }
}

impl<'s> ExpParser<'s> {
  pub fn new(tokens: Tokenizer<'s>) -> ExpParser<'s> {
    let tokens = tokens.peekable();
    ExpParser{tokens, cur: None, trace: false, depth: 0}
  }

  pub fn next(&mut self) -> Result<(), (ExpError, Span)> {
    self.cur = match self.tokens.next() {
      None => unreachable!(),
      Some((tok, span)) => Some((tok, span))
    };
    Ok(())
  }

  pub fn peek_next(&mut self) -> Option<&Token> {
    self.tokens.peek().map(|&(ref tok, _)| tok)
  }

  pub fn peek_next_(&mut self) -> (Token, Span) {
  //pub fn peek_next_(&mut self) -> Result<(Token, Span), (ExpError, Span)> {}
    // FIXME FIXME
    match self.tokens.peek().map(|&(ref tok, span)| (tok.clone(), span))
    {
      None => (Token::_Eof, Span::default()),
      Some((tok, span)) => (tok, span)
    }
  }

  pub fn current(&self) -> Token {
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
      &Token::LBrack => 900,
      &Token::Space => 9999,
      _ => 0
    }
  }

  pub fn maybe_skip_space(&mut self) -> Result<bool, (ExpError, Span)> {
    match self.current_ref() {
      &Token::Space => {}
      _ => return Ok(false)
    }
    loop {
      match self.peek_next() {
        Some(&Token::Space) => {
          self.next()?;
          match self.current_ref() {
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
      Token::Space => {}
      t => {
        if self.trace { self.depth -= 1; }
        return Err((ExpError::ExpectedSpace(t), self.current_span()));
      }
    }
    loop {
      match self.peek_next() {
        Some(&Token::Space) => {
          self.next()?;
          match self.current_ref() {
            &Token::Space => {}
            _ => unreachable!()
          }
        }
        _ => return Ok(())
      }
    }
  }

  pub fn pat(&mut self, ctxbp: i16) -> Result<Exp, (ExpError, Span)> {
    unimplemented!();
  }

  pub fn exp_led(&mut self, ctx: ExpCtx, lexp: Exp, tok: Token, span: Span, /*prespace: bool*/) -> Result<Exp, (ExpError, Span)> {
    if self.trace { self.depth += 1; }
    let lbp = self.lbp(&tok);
    if self._trace2("exp", "led") { println!("lexp={:?} tok={:?} span={:?} lbp={}", lexp, tok, span, lbp); }
    match tok {
      Token::LRParen |
      Token::LParen |
      Token::RParen |
      Token::LRBrack |
      Token::RBrack |
      Token::LRCurly |
      Token::LCurly |
      Token::RCurly => {
        if self.trace { self.depth -= 1; }
        Err((ExpError::InvalidLed(tok), span))
      }
      // TODO TODO
      Token::Plus => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        if ctx == ExpCtx::Parens {
          match self.current() {
            Token::RParen => {
              //self.next()?;
              if self.trace { self.depth -= 1; }
              return Ok(Exp::InfixPartR(lexp.into(), InfixOp::Add));
            }
            _ => {}
          }
        }
        let rexp = self.exp(lbp)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        Ok(Exp::Add(lexp.into(), rexp.into()))
      }
      Token::Dash => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        if ctx == ExpCtx::Parens {
          match self.current() {
            Token::RParen => {
              //self.next()?;
              if self.trace { self.depth -= 1; }
              return Ok(Exp::InfixPartR(lexp.into(), InfixOp::Sub));
            }
            _ => {}
          }
        }
        let rexp = self.exp(lbp)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        Ok(Exp::Sub(lexp.into(), rexp.into()))
      }
      Token::Star => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        if ctx == ExpCtx::Parens {
          match self.current() {
            Token::RParen => {
              //self.next()?;
              if self.trace { self.depth -= 1; }
              return Ok(Exp::InfixPartR(lexp.into(), InfixOp::Mul));
            }
            _ => {}
          }
        }
        let rexp = self.exp(lbp)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        Ok(Exp::Mul(lexp.into(), rexp.into()))
      }
      Token::Slash => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        if ctx == ExpCtx::Parens {
          match self.current() {
            Token::RParen => {
              //self.next()?;
              if self.trace { self.depth -= 1; }
              return Ok(Exp::InfixPartR(lexp.into(), InfixOp::Div));
            }
            _ => {}
          }
        }
        let rexp = self.exp(lbp)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        Ok(Exp::Div(lexp.into(), rexp.into()))
      }
      Token::Percent => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        if ctx == ExpCtx::Parens {
          match self.current() {
            Token::RParen => {
              //self.next()?;
              if self.trace { self.depth -= 1; }
              return Ok(Exp::InfixPartR(lexp.into(), InfixOp::Rem));
            }
            _ => {}
          }
        }
        let rexp = self.exp(lbp)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        Ok(Exp::Rem(lexp.into(), rexp.into()))
      }
      Token::InfixIdent(name) => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        // FIXME
        let name_bytes = name.as_str().as_bytes();
        if name_bytes[0] != b'`' || name_bytes[name_bytes.len() - 1] != b'`' {
          if self.trace { self.depth -= 1; }
          return Err((ExpError::Failed(Token::InfixIdent(name)), span));
        }
        let name = from_utf8(&name_bytes[1 .. name_bytes.len() - 1]).unwrap().into();
        if ctx == ExpCtx::Parens {
          match self.current() {
            Token::RParen => {
              //self.next()?;
              if self.trace { self.depth -= 1; }
              return Ok(Exp::InfixPartR(lexp.into(), InfixOp::Id(name)));
            }
            _ => {}
          }
        }
        let rexp = self.exp(lbp)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        Ok(Exp::InfixApp(InfixOp::Id(name), lexp.into(), rexp.into()))
      }
      Token::LBrack => {
        unimplemented!();
      }
      _ => panic!("bug: led: unimplemented: lexp={:?} tok={:?} span={:?}", lexp, tok, span)
    }
  }

  pub fn exp_nud(&mut self, ctx: ExpCtx, tok: Token, span: Span) -> Result<Exp, (ExpError, Span)> {
    if self.trace { self.depth += 1; }
    if self._trace2("exp", "nud") { println!("tok={:?} span={:?}", tok, span); }
    match tok {
      Token::Space |
      Token::In |
      Token::RParen |
      Token::RBrack |
      Token::RCurly => {
        if self.trace { self.depth -= 1; }
        return Err((ExpError::InvalidNud(tok), span));
      }
      Token::Plus => {
        if ctx != ExpCtx::Parens {
          if self.trace { self.depth -= 1; }
          return Err((ExpError::InvalidNud(tok), span));
        }
        if self.trace { self.depth -= 1; }
        return Ok(Exp::InfixOp(InfixOp::Add));
      }
      Token::Star => {
        if ctx != ExpCtx::Parens {
          if self.trace { self.depth -= 1; }
          return Err((ExpError::InvalidNud(tok), span));
        }
        if self.trace { self.depth -= 1; }
        return Ok(Exp::InfixOp(InfixOp::Mul));
      }
      Token::Slash => {
        if ctx != ExpCtx::Parens {
          if self.trace { self.depth -= 1; }
          return Err((ExpError::InvalidNud(tok), span));
        }
        if self.trace { self.depth -= 1; }
        return Ok(Exp::InfixOp(InfixOp::Div));
      }
      Token::Percent => {
        if ctx != ExpCtx::Parens {
          if self.trace { self.depth -= 1; }
          return Err((ExpError::InvalidNud(tok), span));
        }
        if self.trace { self.depth -= 1; }
        return Ok(Exp::InfixOp(InfixOp::Rem));
      }
      Token::InfixIdent(name) => {
        if ctx != ExpCtx::Parens {
          if self.trace { self.depth -= 1; }
          return Err((ExpError::InvalidNud(Token::InfixIdent(name)), span));
        }
        let name_bytes = name.as_str().as_bytes();
        if name_bytes[0] != b'`' || name_bytes[name_bytes.len() - 1] != b'`' {
          if self.trace { self.depth -= 1; }
          return Err((ExpError::Failed(Token::InfixIdent(name)), span));
        }
        let name = from_utf8(&name_bytes[1 .. name_bytes.len() - 1]).unwrap().into();
        if self.trace { self.depth -= 1; }
        return Ok(Exp::InfixOp(InfixOp::Id(name)));
      }
      // TODO TODO
      Token::Backslash => {
        let mut vars = Vec::new();
        loop {
          if self.maybe_skip_space()? {
            self.next()?;
          }
          let var = self.current().expected_ident(self)?;
          vars.push(var);
          self.next()?;
          if self.maybe_skip_space()? {
            self.next()?;
          }
          match self.current() {
            Token::LArrow => {
              self.next()?;
              break;
            }
            _ => {}
          }
        }
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let body = self.exp(0)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        return Ok(Exp::LamAlt(vars, body.into()));
      }
      Token::Dash => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        let body = self.exp(9999)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        return Ok(Exp::Neg(body.into()));
      }
      Token::LParen => {
        if self.maybe_skip_space()? {
          self.next()?;
        }
        match self.current_ref() {
          &Token::Backslash => {
            let (tok, span) = self.current_();
            self.next()?;
            let (lam_vars, lam_body) = match self.exp_nud(ExpCtx::Top, tok, span)
                .map_err(|e| { if self.trace { self.depth -= 1; } e})?
            {
              Exp::LamAlt(vars, body) => (vars, body),
              _ => {
                if self.trace { self.depth -= 1; }
                return Err((ExpError::Failed(Token::Backslash), span));
              }
            };
            if self.maybe_skip_space()? {
              self.next()?;
            }
            self.current().expected(Token::RParen, self)?;
            self.next()?;
            if self.trace { self.depth -= 1; }
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
                if self.trace { self.depth -= 1; }
                return Ok(Exp::InfixOp(InfixOp::Sub));
                //return Ok(Exp::PrefixOp(PrefixOp::Neg));
              }
              _ => {}
            }
            let neg_inner = match self.exp_nud(ExpCtx::Top, tok, span)
                .map_err(|e| { if self.trace { self.depth -= 1; } e})?
            {
              Exp::Neg(inner) => inner,
              _ => {
                if self.trace { self.depth -= 1; }
                return Err((ExpError::Failed(Token::Dash), span));
              }
            };
            if self.maybe_skip_space()? {
              self.next()?;
            }
            self.current().expected(Token::RParen, self)?;
            self.next()?;
            if self.trace { self.depth -= 1; }
            return Ok(Exp::Neg(neg_inner));
          }
          /*&Token::Plus |
          &Token::Star |
          &Token::Slash |
          &Token::InfixIdent(_) => {
            //if self.trace { println!("TRACE: nud: LParen: infix op..."); }
            let lexp = match self.current() {
              Token::Plus => Exp::InfixOp(InfixOp::Add),
              Token::Star => Exp::InfixOp(InfixOp::Mul),
              Token::Slash => Exp::InfixOp(InfixOp::Div),
              Token::Percent => Exp::InfixOp(InfixOp::Rem),
              Token::InfixIdent(name) => Exp::InfixOp(InfixOp::Id(name)),
              _ => unreachable!()
            };
            //if self.trace { println!("TRACE: nud: LParen:   lexp={:?}", lexp); }
            self.next()?;
            let (tok, span) = self.current_();
            //if self.trace { println!("TRACE: nud: LParen:   tok={:?} span={:?}", tok, span); }
            let lexp = self.exp_rec_(ExpCtx::Parens, 9999, lexp, (tok, span), /*false*/)
                .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
            //if self.trace { println!("TRACE: nud: LParen:   return {:?}", lexp); }
            if self.maybe_skip_space()? {
              self.next()?;
            }
            self.current().expected(Token::RParen, self)?;
            self.next()?;
            if self.trace { self.depth -= 1; }
            return Ok(lexp);
          }*/
          _ => {}
        }
        let inner = self.exp_(ExpCtx::Parens, 0, false)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.maybe_skip_space()? {
          self.next()?;
        }
        self.current().expected(Token::RParen, self)?;
        self.next()?;
        if self.trace { self.depth -= 1; }
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
        //if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        //if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        let name = self.current().expected_ident(self)?;
        //if self.trace { println!("TRACE: nud: Let: name={:?}", name); }
        self.next()?;
        //if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        self.skip_space()?;
        //if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        //if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        self.current().expected(Token::Equals, self)?;
        //if self.trace { println!("TRACE: nud: Let: ="); }
        self.next()?;
        //if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        self.skip_space()?;
        //if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        //if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        let body = self.exp(0)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        //if self.trace { println!("TRACE: nud: Let: body={:?}", body); }
        self.skip_space()?;
        //if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        self.current().expected(Token::In, self)?;
        //if self.trace { println!("TRACE: nud: Let: in"); }
        self.next()?;
        //if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        self.skip_space()?;
        //if self.trace { println!("TRACE: nud: Let: skip space"); }
        self.next()?;
        //if self.trace { println!("TRACE: nud: Let:   next tok={:?}", self.current_ref()); }
        let rest = self.exp(0)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        //if self.trace { println!("TRACE: nud: Let: rest={:?}", rest); }
        if self.trace { self.depth -= 1; }
        return Ok(Exp::Let(name, body.into(), rest.into()));
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
        if self.trace { self.depth -= 1; }
        return Ok(Exp::FloatLit(lit, kind, ty));
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
        if self.trace { self.depth -= 1; }
        return Ok(Exp::IntLit(lit, kind, ty));
      }
      Token::Ident(name) => {
        if self.trace { self.depth -= 1; }
        return Ok(Exp::Id(name));
      }
      _ => panic!("bug: nud: unimplemented: tok={:?} span={:?}", tok, span)
    }
  }

  pub fn exp_(&mut self, ctx: ExpCtx, ctxbp: i16, /*no_fail: bool,*/ only_nud: bool) -> Result<Exp, (ExpError, Span)> {
    if self.trace { self.depth += 1; }
    let mut tok_span = self.current_();
    if self._trace("exp") { println!("enter: tok={:?} span={:?} ctxbp={} only_nud={:?}", tok_span.0, tok_span.1, ctxbp, only_nud); }
    if tok_span.0.is_eof() {
      if self._trace("exp") { println!("fail: eof (1)"); }
      if self.trace { self.depth -= 1; }
      return Err((ExpError::Eof, tok_span.1));
    }
    if tok_span.0.is_space() {
      self.next()?;
      tok_span = self.current_();
      if self._trace("exp") { println!("next tok={:?} (space)", self.current_ref()); }
    }
    if tok_span.0.is_eof() {
      if self._trace("exp") { println!("fail: eof (2)"); }
      if self.trace { self.depth -= 1; }
      return Err((ExpError::Eof, tok_span.1));
    }
    self.next()?;
    if self._trace("exp") { println!("next tok={:?}", self.current_ref()); }
    let nud_ctx = if ctx == ExpCtx::Parens { ctx } else { ExpCtx::Top };
    let lexp = match self.exp_nud(nud_ctx, tok_span.0, tok_span.1) {
      Err(e) => {
        if self._trace("exp") { println!("nud fail: {:?}", e); }
        if self.trace { self.depth -= 1; }
        return Err(e);
      }
      Ok(exp) => exp
    };
    if self._trace("exp") { println!("lexp={:?} (nud)", lexp); }
    tok_span = self.current_();
    if self._trace("exp") { println!("tok={:?} span={:?}", tok_span.0, tok_span.1); }
    if tok_span.0.is_eof() {
      if self._trace("exp") { println!("return {:?}", lexp); }
      if self.trace { self.depth -= 1; }
      return Ok(lexp);
    }
    /*while ctxbp < self.lbp(&tok_span.0) {
      self.next()?;
      lexp = self.exp_led(lexp, tok_span.0, tok_span.1)?;
      tok_span = self.current_();
      if tok_span.0.is_eof() {
        return Ok(lexp);
      }
    }*/
    if !only_nud {
      if self._trace("exp") { println!("try rec..."); }
      let result = self.exp_rec_(ctx, ctxbp, lexp, tok_span, /*no_fail*/);
      if self._trace("exp") { println!("rec result={:?}", &result); }
      if self.trace { self.depth -= 1; }
      return result;
    }
    if self._trace("exp") { println!("return {:?} (only nud)", lexp); }
    if self.trace { self.depth -= 1; }
    Ok(lexp)
  }

  pub fn exp_rec_(&mut self, ctx: ExpCtx, ctxbp: i16, mut lexp: Exp, mut tok_span: (Token, Span), /*no_fail: bool*/) -> Result<Exp, (ExpError, Span)> {
    if self.trace { self.depth += 1; }
    if self._trace2("exp", "rec") { println!("enter: lexp={:?} tok={:?} span={:?} ctxbp={}", &lexp, &tok_span.0, &tok_span.1, ctxbp); }
    /*if no_fail {
      if self._trace2("exp", "rec") { println!("no_fail"); }
    }*/
    loop {
      let mut lbp = self.lbp(&tok_span.0);
      if self._trace2("exp", "rec") { println!("tok={:?}", &tok_span.0); }
      if self._trace2("exp", "rec") { println!("lbp={}", lbp); }
      let mut prespace = false;
      let mut only_led = false;
      let mut only_rec = false;
      if tok_span.0.is_space() {
        tok_span = self.peek_next_();
        assert!(!tok_span.0.is_space());
        if tok_span.0.is_eof() {
          if self._trace2("exp", "rec") { println!("return {:?}", &lexp); }
          if self.trace { self.depth -= 1; }
          return Ok(lexp);
        }
        lbp = self.lbp(&tok_span.0);
        if self._trace2("exp", "rec") { println!("tok={:?} (prespace)", &tok_span.0); }
        if self._trace2("exp", "rec") { println!("lbp={} (prespace)", lbp); }
        prespace = true;
        if let &Token::LBrack = &tok_span.0 {
          only_rec = true;
        }
      }
      if let &Token::Dash = &tok_span.0 {
        only_led = true;
      }
      if only_led {
        if self._trace2("exp", "rec") { println!("only_led"); }
      }
      if only_rec {
        if self._trace2("exp", "rec") { println!("only_rec"); }
      }
      let mut mat = false;
      let mut err_led = None;
      let mut err_rec = None;
      let mut fail_led = false;
      if !only_rec && ctxbp < lbp {
        if self._trace2("exp", "rec") { println!("led: try: lexp={:?} ctxbp={} < lbp={}", &lexp, ctxbp, lbp); }
        let mut parser = self.clone();
        if prespace {
          parser.next()?;
          if self._trace2("exp", "rec") { println!("led: next tok={:?} (prespace)", self.current_ref()); }
        }
        parser.next()?;
        if self._trace2("exp", "rec") { println!("led: next tok={:?}", self.current_ref()); }
        let led_ctx = if ctx == ExpCtx::Parens { ctx } else { ExpCtx::Top };
        match parser.exp_led(led_ctx, lexp.clone(), tok_span.0.clone(), tok_span.1, /*prespace*/) {
          Err(e) => {
            if self._trace2("exp", "rec") { println!("led: failed tok={:?} only_led={:?}: {:?}", &tok_span.0, only_led, e); }
            err_led = Some(e);
            fail_led = true;
          }
          Ok(led_exp) => {
            *self = parser;
            lexp = led_exp;
            tok_span = self.current_();
            if self._trace2("exp", "rec") { println!("led: lexp={:?}", &lexp); }
            if self._trace2("exp", "rec") { println!("led: tok={:?}", &tok_span.0); }
            if tok_span.0.is_eof() {
              if self._trace2("exp", "rec") { println!("return {:?}", &lexp); }
              if self.trace { self.depth -= 1; }
              return Ok(lexp);
            }
            mat = true;
          }
        }
      }
      if !only_led && (fail_led || ctxbp >= lbp) {
        if self._trace2("exp", "rec") { println!("backtrack: try: lexp={:?} fail_led={:?} ctxbp={} lbp={}", &lexp, fail_led, ctxbp, lbp); }
        let mut parser = self.clone();
        if self._trace2("exp", "rec") { println!("backtrack: tok={:?}", &tok_span.0); }
        if self._trace2("exp", "rec") { println!("backtrack: prespace?{:?}", prespace); }
        if self._trace2("exp", "rec") { println!("backtrack: cur={:?}", parser.current_ref()); }
        if self._trace2("exp", "rec") { println!("backtrack: peek next={:?}", parser.peek_next()); }
        if prespace {
          parser.next()?;
          if self._trace2("exp", "rec") { println!("backtrack: next tok={:?} (prespace)", parser.current_ref()); }
        }
        let rec_ctx = if ctx == ExpCtx::Parens { ctx } else { ExpCtx::Top };
        match parser.exp_(rec_ctx, 9999, /*false,*/ true) {
          Err(e) => {
            if self._trace2("exp", "rec") { println!("backtrack: failed: {:?}", e); }
            err_rec = Some(e);
          }
          Ok(arg_exp) => {
            *self = parser;
            if self._trace2("exp", "rec") { println!("backtrack: return {:?}", &arg_exp); }
            lexp = Exp::App(lexp.into(), arg_exp.into());
            tok_span = self.current_();
            if self._trace2("exp", "rec") { println!("backtrack: lexp={:?}", &lexp); }
            if self._trace2("exp", "rec") { println!("backtrack: tok={:?}", &tok_span.0); }
            if tok_span.0.is_eof() {
              if self._trace2("exp", "rec") { println!("return {:?}", lexp); }
              if self.trace { self.depth -= 1; }
              return Ok(lexp);
            }
            mat = true;
          }
        }
      }
      if !mat {
        if err_led.is_some() || err_rec.is_some() {
          //println!("no mat and err");
          if let Some(ref e) = err_led {
            if self._trace2("exp", "rec") { println!("err led={:?}", e); }
          }
          if let Some(ref e) = err_rec {
            if self._trace2("exp", "rec") { println!("err rec={:?}", e); }
          }
        }
        if ctx == ExpCtx::Root &&
           ((!only_rec && err_led.is_some()) ||
            (!only_led && err_rec.is_some()))
        {
          if self._trace2("exp", "rec") { println!("fail"); }
          if self.trace { self.depth -= 1; }
          return Err(err_led.or(err_rec).unwrap());
        }
        break;
      }
    }
    if self._trace2("exp", "rec") { println!("return {:?}", lexp); }
    if self.trace { self.depth -= 1; }
    Ok(lexp)
  }

  pub fn exp(&mut self, ctxbp: i16) -> Result<Exp, (ExpError, Span)> {
    self.exp_(ExpCtx::Top, ctxbp, /*false,*/ false)
  }

  pub fn root_exp(&mut self, ctxbp: i16) -> Result<Exp, (ExpError, Span)> {
    self.exp_(ExpCtx::Root, ctxbp, /*true,*/ false)
  }

  pub fn _trace2(&self, prefix: &str, suffix: &str) -> bool {
    if self.trace {
      print!("TRACE: {}/{}: ", prefix, suffix);
      assert!(self.depth > 0);
      for _ in 1 .. self.depth {
        print!("  ");
      }
    }
    self.trace
  }

  pub fn _trace(&self, prefix: &str) -> bool {
    if self.trace {
      print!("TRACE: {}    : ", prefix);
      assert!(self.depth > 0);
      for _ in 1 .. self.depth {
        print!("  ");
      }
    }
    self.trace
  }

  pub fn trace(mut self) -> ExpParser<'s> {
    self.trace = true;
    self.depth = 0;
    self
  }

  pub fn parse(mut self) -> Result<Exp, (ExpError, Span)> {
    self.next()?;
    self.root_exp(0)
  }
}
