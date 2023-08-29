use crate::tokenizing::*;

use smol_str::{SmolStr};

use std::iter::{Peekable};
use std::rc::{Rc};
use std::str::{from_utf8};

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
    let mut this = ExpParser{tokens, cur: None, trace: false, depth: 0};
    this.next().unwrap();
    this
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

  pub fn maybe_skip_space(&mut self) -> Result<bool, (ExpError, Span)> {
    match self.current_ref() {
      &Token::Space => {
        self.next()?;
      }
      _ => return Ok(false)
    }
    loop {
      match self.current_ref() {
        &Token::Space => {
          self.next()?;
        }
        _ => return Ok(true)
      }
    }
  }

  pub fn skip_space(&mut self) -> Result<(), (ExpError, Span)> {
    match self.current() {
      Token::Space => {
        self.next()?;
      }
      t => {
        if self.trace { self.depth -= 1; }
        return Err((ExpError::ExpectedSpace(t), self.current_span()));
      }
    }
    loop {
      match self.current_ref() {
        &Token::Space => {
          self.next()?;
        }
        _ => return Ok(())
      }
    }
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
        self.maybe_skip_space()?;
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
        self.maybe_skip_space()?;
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
        self.maybe_skip_space()?;
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
        self.maybe_skip_space()?;
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
        self.maybe_skip_space()?;
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
        self.maybe_skip_space()?;
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
          self.maybe_skip_space()?;
          let var = self.current().expected_ident(self)?;
          vars.push(var);
          self.next()?;
          self.maybe_skip_space()?;
          match self.current() {
            Token::LArrow => {
              self.next()?;
              break;
            }
            _ => {}
          }
        }
        self.maybe_skip_space()?;
        let body = self.exp(0)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        return Ok(Exp::LamAlt(vars, body.into()));
      }
      Token::Dash => {
        self.maybe_skip_space()?;
        let body = self.exp(9999)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        if self.trace { self.depth -= 1; }
        return Ok(Exp::Neg(body.into()));
      }
      Token::LParen => {
        self.maybe_skip_space()?;
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
            self.maybe_skip_space()?;
            self.current().expected(Token::RParen, self)?;
            self.next()?;
            if self.trace { self.depth -= 1; }
            return Ok(Exp::Lam(lam_vars, lam_body));
          }
          &Token::Dash => {
            let (tok, span) = self.current_();
            self.next()?;
            // FIXME
            let prespace = self.maybe_skip_space()?;
            let next_tok_span = self.current_();
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
            self.maybe_skip_space()?;
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
            self.maybe_skip_space()?;
            self.current().expected(Token::RParen, self)?;
            self.next()?;
            if self.trace { self.depth -= 1; }
            return Ok(lexp);
          }*/
          _ => {}
        }
        let inner = self.exp_(ExpCtx::Parens, 0, false)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        self.maybe_skip_space()?;
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
        let name = self.current().expected_ident(self)?;
        self.next()?;
        self.skip_space()?;
        self.current().expected(Token::Equals, self)?;
        self.next()?;
        self.skip_space()?;
        let body = self.exp(0)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
        self.skip_space()?;
        self.current().expected(Token::In, self)?;
        self.next()?;
        self.skip_space()?;
        let rest = self.exp(0)
            .map_err(|e| { if self.trace { self.depth -= 1; } e})?;
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
    self.root_exp(0)
  }
}
