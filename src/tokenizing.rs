use crate::re::{ReTrie};

use smol_str::{SmolStr};

use std::borrow::{Cow};
use std::cmp::{Ordering, max, min};
use std::rc::{Rc};

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
