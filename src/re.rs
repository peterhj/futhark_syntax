use regex_syntax::hir::{HirKind as ReExpKind, Hir as ReExp, Class as ReClass, Literal as ReLiteral, RepetitionKind};

use std::collections::{BTreeMap, BTreeSet};

pub struct ReMultiMapValues<'a, K, V> {
  x:    Option<V>,
  k:    K,
  ch:   &'a BTreeMap<(K, V), V>,
}

impl<'a, K: Copy + Ord, V: Copy + Ord> Iterator for ReMultiMapValues<'a, K, V> {
  type Item = V;

  fn next(&mut self) -> Option<V> {
    match self.x {
      None => None,
      Some(x) => {
        match self.ch.get(&(self.k, x)) {
          None => unreachable!(),
          Some(&nx) => if x == nx {
            self.x = None;
          } else {
            self.x = Some(nx);
          }
        }
        Some(x)
      }
    }
  }
}

#[derive(Default)]
pub struct ReMultiMap<K: Copy + Ord, V: Copy + Ord> {
  rt:   BTreeMap<K, (V, V)>,
  ch:   BTreeMap<(K, V), V>,
}

impl<K: Copy + Ord, V: Copy + Ord> ReMultiMap<K, V> {
  pub fn keys<'a>(&'a self) -> impl Iterator<Item=K> + 'a {
    self.rt.keys().map(|&k| k)
  }

  pub fn values<'a>(&'a self, k: K) -> impl Iterator<Item=V> + 'a {
    match self.rt.get(&k) {
      None => ReMultiMapValues{
        x:  None,
        k,
        ch: &self.ch,
      },
      Some(&(x, _)) => ReMultiMapValues{
        x:  Some(x),
        k,
        ch: &self.ch,
      }
    }
  }

  pub fn insert(&mut self, k: K, v: V) {
    match self.rt.get(&k) {
      None => {
        self.rt.insert(k, (v, v));
        self.ch.insert((k, v), v);
      }
      Some(&(lb, ub)) => {
        self.rt.insert(k, (lb, v));
        self.ch.insert((k, ub), v);
        self.ch.insert((k, v), v);
      }
    }
  }
}

pub struct ReTrie<T> {
  inner:    ReInnerTrie,
  postfuns: Vec<Box<dyn Fn(&str) -> T>>,
  //ctrl_fun: Option<Box<dyn Fn(char) -> T>>,
}

impl<T> Default for ReTrie<T> {
  fn default() -> ReTrie<T> {
    ReTrie{
      inner:    ReInnerTrie::default(),
      postfuns: Vec::new(),
      //ctrl_fun: None,
    }
  }
}

impl<T> ReTrie<T> {
  /*pub fn reset_control_fallback<F: 'static + Fn(char) -> T>(&mut self, fun: F) {
    self.ctrl_fun = Some(Box::new(fun));
  }

  pub fn unset_control_fallback(&mut self) {
    self.ctrl_fun = None;
  }*/

  pub fn push<F: 'static + Fn(&str) -> T>(&mut self, rexp: ReExp, postfun: F) {
    let ridx = self.postfuns.len();
    match rexp.kind() {
      &ReExpKind::Concat(ref rexps) => {
        assert!(!rexps.is_empty());
        let (rexp, rexps) = rexps.split_first().unwrap();
        self.inner._push(rexp, rexps, ridx);
      }
      &ReExpKind::Literal(_) => {
        self.inner._push(&rexp, &[], ridx);
      }
      &ReExpKind::Class(_) => {
        self.inner._push(&rexp, &[], ridx);
      }
      &ReExpKind::Repetition(_) => {
        self.inner._push(&rexp, &[], ridx);
      }
      _ => unimplemented!()
    }
    self.postfuns.push(Box::new(postfun));
  }

  pub fn split_match<'t>(&self, text: &'t str) -> Option<(T, &'t str)> {
    let (mat_len, ridx) = self.inner._match(text, None, /*0*/)?;
    let (tok, rem) = text.split_at(mat_len);
    Some((self.postfuns[ridx](tok), rem))
  }

  pub fn match_at<'t>(&self, text: &'t str, pos: usize) -> Option<(T, usize)> {
    let search = match text.get(pos .. ) {
      None => panic!("bug"),
      Some(s) => s
    };
    let (mat_len, ridx) = self.inner._match(search, None, /*0*/)?;
    /*if mat.is_none() {
      if let Some(ref ctrl_fun) = self.ctrl_fun.as_ref() {
        if c.is_control() {
          return Some(((ctrl_fun)(c), next_pos));
        }
      }
    }*/
    let (tok, _) = search.split_at(mat_len);
    Some((self.postfuns[ridx](tok), pos + mat_len))
  }
}

enum ReInnerTrieRef {
  Terminal(usize),
  Trie(ReInnerTrie),
}

#[derive(Default)]
struct ReInnerTrie {
  index:    Option<usize>,
  zero:     BTreeSet<usize>,
  lit_term: ReMultiMap<char, usize>,
  literal:  BTreeMap<char, ReInnerTrie>,
  klass:    ReMultiMap<(char, char), usize>,
  bound1:   ReMultiMap<(char, char), usize>,
  unbound:  ReMultiMap<(char, char), usize>,
  ranges:   BTreeMap<usize, Vec<(char, char)>>,
  non_lit:  Vec<ReInnerTrieRef>,
}

impl ReInnerTrie {
  fn new(index: usize) -> ReInnerTrie {
    let mut trie = ReInnerTrie::default();
    trie.index = Some(index);
    trie
  }

  fn _push(&mut self, rexp: &ReExp, rexps: &[ReExp], ridx: usize) {
    if let Some(idx) = self.index {
      if idx != ridx {
        self.index = None;
      }
    }
    match rexp.kind() {
      &ReExpKind::Literal(ref re_lit) => {
        let c = match re_lit {
          &ReLiteral::Unicode(c) => c,
          &ReLiteral::Byte(x) => if x.is_ascii() {
            char::from(x)
          } else {
            panic!("bug: re: non-ascii u8 to char: {:x}", x)
          }
        };
        if rexps.is_empty() {
          self.lit_term.insert(c, ridx);
        } else {
          if !self.literal.contains_key(&c) {
            self.literal.insert(c, ReInnerTrie::new(ridx));
          }
          let (rexp, rexps) = rexps.split_first().unwrap();
          self.literal.get_mut(&c).unwrap()._push(rexp, rexps, ridx);
        }
      }
      &ReExpKind::Class(ref re_klass) => {
        match re_klass {
          &ReClass::Unicode(ref klass) => {
            let eidx = self.non_lit.len();
            let mut ranges = Vec::new();
            for range in klass.ranges() {
              let lb = range.start();
              let ub = range.end();
              self.klass.insert((lb, ub), eidx);
              ranges.push((lb, ub));
            }
            self.ranges.insert(eidx, ranges);
            if rexps.is_empty() {
              self.non_lit.push(ReInnerTrieRef::Terminal(ridx));
            } else {
              self.non_lit.push(ReInnerTrieRef::Trie(ReInnerTrie::new(ridx)));
              let (rexp, rexps) = rexps.split_first().unwrap();
              match &mut self.non_lit[eidx] {
                &mut ReInnerTrieRef::Terminal(_) => unreachable!(),
                &mut ReInnerTrieRef::Trie(ref mut trie) => {
                  trie._push(rexp, rexps, ridx);
                }
              }
            }
          }
          _ => unimplemented!()
        }
      }
      &ReExpKind::Repetition(ref re_rep) => {
        assert!(re_rep.greedy);
        let (zero, unbound) = match &re_rep.kind {
          &RepetitionKind::ZeroOrOne => (true, false),
          &RepetitionKind::ZeroOrMore => (true, true),
          &RepetitionKind::OneOrMore => (false, true),
          _ => unimplemented!()
        };
        match re_rep.hir.kind() {
          &ReExpKind::Literal(ref re_lit) => {
            let eidx = self.non_lit.len();
            if zero {
              self.zero.insert(eidx);
            } else {
              //self.repeat1.insert(eidx);
            }
            let mut ranges = Vec::new();
            let c = match re_lit {
              &ReLiteral::Unicode(c) => c,
              _ => unimplemented!()
            };
            if unbound {
              self.unbound.insert((c, c), eidx);
            } else {
              self.bound1.insert((c, c), eidx);
            }
            ranges.push((c, c));
            self.ranges.insert(eidx, ranges);
            if rexps.is_empty() {
              self.non_lit.push(ReInnerTrieRef::Terminal(ridx));
            } else {
              self.non_lit.push(ReInnerTrieRef::Trie(ReInnerTrie::new(ridx)));
              let (rexp, rexps) = rexps.split_first().unwrap();
              match &mut self.non_lit[eidx] {
                &mut ReInnerTrieRef::Terminal(_) => unreachable!(),
                &mut ReInnerTrieRef::Trie(ref mut trie) => {
                  trie._push(rexp, rexps, ridx);
                }
              }
            }
          }
          &ReExpKind::Class(ref re_klass) => match re_klass {
            &ReClass::Unicode(ref klass) => {
              let eidx = self.non_lit.len();
              if zero {
                self.zero.insert(eidx);
              } else {
                //self.repeat1.insert(eidx);
              }
              let mut ranges = Vec::new();
              for range in klass.ranges() {
                let lb = range.start();
                let ub = range.end();
                if unbound {
                  self.unbound.insert((lb, ub), eidx);
                } else {
                  self.bound1.insert((lb, ub), eidx);
                }
                ranges.push((lb, ub));
              }
              self.ranges.insert(eidx, ranges);
              if rexps.is_empty() {
                self.non_lit.push(ReInnerTrieRef::Terminal(ridx));
              } else {
                self.non_lit.push(ReInnerTrieRef::Trie(ReInnerTrie::new(ridx)));
                let (rexp, rexps) = rexps.split_first().unwrap();
                match &mut self.non_lit[eidx] {
                  &mut ReInnerTrieRef::Terminal(_) => unreachable!(),
                  &mut ReInnerTrieRef::Trie(ref mut trie) => {
                    trie._push(rexp, rexps, ridx);
                  }
                }
              }
            }
            _ => unimplemented!()
          }
          _ => unimplemented!()
        }
      }
      _ => unimplemented!()
    }
  }

  fn _match(&self, text: &str, ctx: Option<usize>, /*depth: i32*/) -> Option<(usize, usize)> {
    match (ctx, self.index) {
      (Some(ctx), Some(idx)) => if ctx != idx {
        //println!("TRACE: re: ctx: {:?} depth: {}, idx: {:?} mismatch", ctx, depth, self.index);
        return None;
      },
      _ => {}
    }
    //let top_ctx = ctx;
    let ctx = ctx.or(self.index);
    let mut chars = text.char_indices();
    let c = match chars.next() {
      None => {
        assert_eq!(text.len(), 0);
        //println!("TRACE: re: ctx: {:?} depth: {} idx: {:?} empty suffix", top_ctx, depth, self.index);
        let mut mat = None;
        for &eidx in self.zero.iter() {
          match &self.non_lit[eidx] {
            &ReInnerTrieRef::Terminal(ridx) => match (ctx, mat) {
              (None, None) => {
                //println!("TRACE: re:   empty: terminal N N");
                mat = Some((0, ridx));
              }
              (None, Some((_, old_idx))) => if ridx < old_idx {
                //println!("TRACE: re:   empty: terminal N S");
                mat = Some((0, ridx));
              }
              (Some(ctx), _) => if ctx == ridx {
                //println!("TRACE: re:   empty: terminal S _");
                mat = Some((0, ridx));
                break;
              }
            }
            &ReInnerTrieRef::Trie(ref trie) => match trie._match(text, ctx, /*depth + 1*/) {
              None => {
                //println!("TRACE: re:   empty: no trie match");
              }
              Some((_, ridx)) => match (ctx, mat) {
                (None, None) => {
                  //println!("TRACE: re:   empty: terminal N N");
                  mat = Some((0, ridx));
                }
                (None, Some((_, old_idx))) => if ridx < old_idx {
                  //println!("TRACE: re:   empty: terminal N S");
                  mat = Some((0, ridx));
                }
                (Some(ctx), _) => if ctx == ridx {
                  //println!("TRACE: re:   empty: terminal S _");
                  mat = Some((0, ridx));
                  break;
                }
              }
            }
          }
        }
        return mat;
      }
      Some((pos, c)) => {
        assert_eq!(pos, 0);
        c
      }
    };
    let next_pos = match chars.next() {
      None => text.len(),
      Some((pos, _)) => pos
    };
    drop(chars);
    let suffix = match text.get(next_pos .. ) {
      None => unreachable!(),
      Some(s) => s
    };
    //println!("TRACE: re: ctx: {:?} depth: {} idx: {:?} char: '{}' suffix: '{}'", top_ctx, depth, self.index, c, suffix);
    let mut mat = None;
    // FIXME: think about this.
    let mut zero_mat = None;
    for &eidx in self.zero.iter() {
      match &self.non_lit[eidx] {
        &ReInnerTrieRef::Terminal(ridx) => match (ctx, zero_mat) {
          ////println!("TRACE: re:   repeat0: terminal ({})", ridx);
          (None, None) => {
            //println!("TRACE: re:   repeat0: terminal N N ({})", ridx);
            zero_mat = Some((0, ridx));
          }
          (None, Some((old_len, old_idx))) => if ridx < old_idx {
            //println!("TRACE: re:   repeat0: terminal N S ({})", ridx);
            assert_eq!(old_len, 0);
            zero_mat = Some((0, ridx));
          }
          (Some(ctx), _) => if ctx == ridx {
            //println!("TRACE: re:   repeat0: terminal S _ ({})", ridx);
            zero_mat = Some((0, ridx));
            break;
          }
        }
        &ReInnerTrieRef::Trie(ref trie) => match trie._match(text, ctx, /*depth + 1*/) {
          None => {
            //println!("TRACE: re:   repeat0: no trie/term match");
          }
          Some((0, ridx)) => match (ctx, zero_mat) {
            ////println!("TRACE: re:   repeat0: trie/term ({})", ridx);
            (None, None) => {
              //println!("TRACE: re:   repeat0: trie/term N N ({})", ridx);
              zero_mat = Some((0, ridx));
            }
            (None, Some((old_len, old_idx))) => if ridx < old_idx {
              //println!("TRACE: re:   repeat0: trie/term N S ({})", ridx);
              assert_eq!(old_len, 0);
              zero_mat = Some((0, ridx));
            }
            (Some(ctx), _) => if ctx == ridx {
              //println!("TRACE: re:   repeat0: trie/term S _ ({})", ridx);
              zero_mat = Some((0, ridx));
              break;
            }
          }
          Some((text_len, ridx)) => match (ctx, mat) {
            (None, None) => {
              //println!("TRACE: re:   repeat0: trie N N");
              mat = Some((text_len, ridx));
            }
            (None, Some((old_len, old_idx))) => if old_len < text_len
                || old_len == text_len && ridx < old_idx {
              //println!("TRACE: re:   repeat0: trie N S");
              mat = Some((text_len, ridx));
            }
            (Some(ctx), _) => if ctx == ridx {
              //println!("TRACE: re:   repeat0: trie S _");
              mat = Some((text_len, ridx));
              //return mat;
              break;
            }
          }
        }
      }
    }
    for ridx in self.lit_term.values(c) {
      match (ctx, mat) {
        (None, None) => {
          //println!("TRACE: re:   literal: terminal N N ({})", ridx);
          mat = Some((1, ridx));
        }
        (None, Some((old_len, old_idx))) => if old_len < 1
            || old_len == 1 && ridx < old_idx {
          //println!("TRACE: re:   literal: terminal N S ({})", ridx);
          mat = Some((1, ridx));
        }
        (Some(ctx), _) => if ctx == ridx {
          //println!("TRACE: re:   literal: terminal S _ ({})", ridx);
          mat = Some((1, ridx));
          return mat;
        }
      }
    }
    if let Some(trie) = self.literal.get(&c) {
      match trie._match(suffix, ctx, /*depth + 1*/) {
        None => {
          //println!("TRACE: re:   literal: no trie match");
        }
        Some((suffix_len, ridx)) => match (ctx, mat) {
          (None, None) => {
            //println!("TRACE: re:   literal: trie N N ({})", ridx);
            mat = Some((1 + suffix_len, ridx));
          }
          (None, Some((old_len, old_idx))) => if old_len < 1 + suffix_len
              || old_len == 1 + suffix_len && ridx < old_idx {
            //println!("TRACE: re:   literal: trie N S ({})", ridx);
            mat = Some((1 + suffix_len, ridx));
          }
          (Some(ctx), _) => if ctx == ridx {
            //println!("TRACE: re:   literal: trie S _ ({})", ridx);
            mat = Some((1 + suffix_len, ridx));
            return mat;
          }
        }
      }
    }
    for (lb, ub) in self.klass.keys() {
      if ub < c {
        continue;
      } else if c < lb {
        break;
      }
      for eidx in self.klass.values((lb, ub)) {
        match &self.non_lit[eidx] {
          &ReInnerTrieRef::Terminal(ridx) => match (ctx, mat) {
            (None, None) => {
              //println!("TRACE: re:   klass: terminal N N");
              mat = Some((1, ridx));
            }
            (None, Some((old_len, old_idx))) => if old_len < 1
                || old_len == 1 && ridx < old_idx {
              //println!("TRACE: re:   klass: terminal N S");
              mat = Some((1, ridx));
            }
            (Some(ctx), _) => if ctx == ridx {
              //println!("TRACE: re:   klass: terminal S _");
              mat = Some((1, ridx));
              return mat;
            }
          }
          &ReInnerTrieRef::Trie(ref trie) => match trie._match(suffix, ctx, /*depth + 1*/) {
            None => {
              //println!("TRACE: re:   klass: no trie match");
            }
            Some((suffix_len, ridx)) => match (ctx, mat) {
              (None, None) => {
                //println!("TRACE: re:   klass: trie N N");
                mat = Some((1 + suffix_len, ridx));
              }
              (None, Some((old_len, old_idx))) => if old_len < 1 + suffix_len
                  || old_len == 1 + suffix_len && ridx < old_idx {
                //println!("TRACE: re:   klass: trie N S");
                mat = Some((1 + suffix_len, ridx));
              }
              (Some(ctx), _) => if ctx == ridx {
                //println!("TRACE: re:   klass: trie S _");
                mat = Some((1 + suffix_len, ridx));
                return mat;
              }
            }
          }
        }
      }
    }
    for (lb, ub) in self.bound1.keys() {
      if ub < c {
        continue;
      } else if c < lb {
        break;
      }
      for eidx in self.bound1.values((lb, ub)) {
        match &self.non_lit[eidx] {
          &ReInnerTrieRef::Terminal(ridx) => match (ctx, mat) {
            (None, None) => {
              //println!("TRACE: re:   bound1: terminal N N");
              mat = Some((1, ridx));
            }
            (None, Some((old_len, old_idx))) => if old_len < 1
                || old_len == 1 && ridx < old_idx {
              //println!("TRACE: re:   bound1: terminal N S");
              mat = Some((1, ridx));
            }
            (Some(ctx), _) => if ctx == ridx {
              //println!("TRACE: re:   bound1: terminal S _");
              mat = Some((1, ridx));
              return mat;
            }
          }
          &ReInnerTrieRef::Trie(ref trie) => match trie._match(suffix, ctx, /*depth + 1*/) {
            None => {
              //println!("TRACE: re:   bound1: no trie match");
            }
            Some((suffix_len, ridx)) => match (ctx, mat) {
              (None, None) => {
                //println!("TRACE: re:   bound1: trie N N");
                mat = Some((1 + suffix_len, ridx));
              }
              (None, Some((old_len, old_idx))) => if old_len < 1 + suffix_len
                  || old_len == 1 + suffix_len && ridx < old_idx {
                //println!("TRACE: re:   bound1: trie N S");
                mat = Some((1 + suffix_len, ridx));
              }
              (Some(ctx), _) => if ctx == ridx {
                //println!("TRACE: re:   bound1: trie S _");
                mat = Some((1 + suffix_len, ridx));
                return mat;
              }
            }
          }
        }
      }
    }
    for (lb, ub) in self.unbound.keys() {
      if ub < c {
        continue;
      } else if c < lb {
        break;
      }
      for eidx in self.unbound.values((lb, ub)) {
        let mut rep_ct = 1;
        let mut suffix = suffix;
        loop {
          let mut chars = suffix.char_indices();
          let c = match chars.next() {
            None => break,
            Some((pos, c)) => {
              assert_eq!(pos, 0);
              c
            }
          };
          let mut more = false;
          for &(lb, ub) in self.ranges.get(&eidx).unwrap().iter() {
            if lb <= c && c <= ub {
              more = true;
              break;
            }
          }
          if !more {
            break;
          }
          rep_ct += 1;
          suffix = match chars.next() {
            None => &suffix[suffix.len() .. ],
            Some((p, _)) => match suffix.get(p .. ) {
              None => unreachable!(),
              Some(s) => s
            }
          };
        }
        match &self.non_lit[eidx] {
          &ReInnerTrieRef::Terminal(ridx) => match (ctx, mat) {
            (None, None) => {
              //println!("TRACE: re:   repeat: terminal N N");
              mat = Some((rep_ct, ridx));
            }
            (None, Some((old_len, old_idx))) => if old_len < rep_ct
                || old_len == rep_ct && ridx < old_idx {
              //println!("TRACE: re:   repeat: terminal N S");
              mat = Some((rep_ct, ridx));
            }
            (Some(ctx), _) => if ctx == ridx {
              //println!("TRACE: re:   repeat: terminal S _");
              mat = Some((rep_ct, ridx));
              return mat;
            }
          }
          &ReInnerTrieRef::Trie(ref trie) => match trie._match(suffix, ctx, /*depth + 1*/) {
            None => {
              //println!("TRACE: re:   repeat: no trie match");
            }
            Some((suffix_len, ridx)) => match (ctx, mat) {
              (None, None) => {
                //println!("TRACE: re:   repeat: trie N N");
                mat = Some((rep_ct + suffix_len, ridx));
              }
              (None, Some((old_len, old_idx))) => if old_len < rep_ct + suffix_len
                  || old_len == rep_ct + suffix_len && ridx < old_idx {
                //println!("TRACE: re:   repeat: trie N S");
                mat = Some((rep_ct + suffix_len, ridx));
              }
              (Some(ctx), _) => if ctx == ridx {
                //println!("TRACE: re:   repeat: trie S _");
                mat = Some((rep_ct + suffix_len, ridx));
                return mat;
              }
            }
          }
        }
      }
    }
    mat = mat.or(zero_mat);
    //println!("TRACE: re: ctx: {:?} depth: {} idx: {:?} char: '{}' suffix: '{}' match: {:?}", top_ctx, depth, self.index, c, suffix, mat);
    mat
  }
}
