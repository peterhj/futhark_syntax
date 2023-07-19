# futhark_syntax

`futhark_syntax` is a Rust crate for parsing [Futhark](https://futhark-lang.org/),
a purely functional language for writing computation kernels.
As of June 2023, the focus of `futhark_syntax` is solely on parsing the
_expression_ fragment of Futhark, i.e. the part of Futhark consisting of
evaluable (and typable) terms.

The Futhark compiler's own lexer and parser are auto-generated from
definitions using Haskell analogs of lex and yacc (alex and happy).
On the other hand, the lexer and parser in `futhark_syntax` are written
from scratch to be self-contained, to facilitate extensions for my
own purposes, as well as for educational purposes.

The lexer (`Tokenizer`) is an ordered set of pattern-matching rules,
where each rule can be thought of as `RegExp -> Token` and is assigned
a unique priority. The tokenization of the source code is then the
sequence of matches of highest priority and of maximal length, i.e. where
ambiguous (multiple) matches are resolved first on the highest priority
among the matching rules, and then on the greatest match length among
those matches of the same rule.

The expression parser (`ExpParser`) is based on [Pratt parsing](https://web.archive.org/web/20071012224713/http://javascript.crockford.com/tdop/tdop.html),
extended with limited depth search and backtracking to parse
left-associative function application via juxtaposition.
