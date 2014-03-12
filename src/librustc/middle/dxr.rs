// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// TODO explain a bit more maybe
// output data for analysis by the dxr rust plugin

// TODO maybe turn this file into a module and break it up

use collections::hashmap::HashMap;

use driver::driver::CrateAnalysis;
use driver::session::Session;

use middle::ty;
use middle::typeck;

use std::cast;
use std::io;
use std::io::File;
use std::io::fs;
use std::os;
use std::path;
use std::str;
use std::vec_ng::Vec;

use syntax::ast;
use syntax::ast_util;
use syntax::ast::{NodeId,DefId};
use syntax::ast_map::{NodeItem};
use syntax::attr;
use syntax::codemap::*;
use syntax::diagnostic;
use syntax::parse::lexer;
use syntax::parse::lexer::{Reader,StringReader};
use syntax::parse::token;
use syntax::parse::token::{get_ident,is_keyword,keywords,is_ident,Token};
use syntax::visit;
use syntax::visit::Visitor;
use syntax::print::pprust::{path_to_str,ty_to_str};

// Helper function to escape quotes in a string
fn escape(s: &str) -> ~str {
    str::replace(s, "\"", "\"\"")
}

// If the expression is a macro expansion or other generated code, run screaming and don't index.
fn generated_code(span: Span) -> bool {
    match span.expn_info {
        Some(_) => return true,
        None => span == DUMMY_SP,
    }
}

struct Recorder {
    // output file
    out: ~Writer,
    dump_spans: bool,
}

impl Recorder {
    fn record(&mut self, info: &str) {
        match write!(self.out, "{}", info) {
            Err(_) => println!("Error writing output '{}'", info),
            _ => (),
        }
    }

    fn dump_span(&mut self, su: SpanUtils, kind: &str, span: Span, _sub_span: Option<Span>) {
        assert!(self.dump_spans);
        self.record(format!("span,kind,{},{},text,\"{}\"\n",
                            kind, su.extent_str(span), escape(su.snippet(span))));
    }
}

struct SpanUtils {
    code_map: @CodeMap,
    err_count: int,
}

impl SpanUtils {
    // Standard string for extents/location.
    // sub_span starts at span.lo, so we need to adjust the positions etc.
    // if sub_span is None, we don't need to adjust.
    fn extent_str(&self, span: Span) -> ~str {
        let lo_loc = self.code_map.lookup_char_pos(span.lo);
        let hi_loc = self.code_map.lookup_char_pos(span.hi);
        let lo_pos = self.code_map.lookup_byte_offset(span.lo).pos;
        let hi_pos = self.code_map.lookup_byte_offset(span.hi).pos;

        format!("file_name,{},file_line,{},file_col,{},extent_start,{},\
                 file_line_end,{},file_col_end,{},extent_end,{}",
                lo_loc.file.name, lo_loc.line, lo_loc.col.to_uint(), lo_pos.to_uint(),
                hi_loc.line, hi_loc.col.to_uint(), hi_pos.to_uint())
    }

    fn make_sub_span(&self, span: Span, sub_span: Option<Span>) -> Option<Span> {
        let loc = self.code_map.lookup_char_pos(span.lo);
        assert!(!generated_code(span),
                "generated code; we should not be processing this `{}` in {}, line {}",
                 self.snippet(span), loc.file.name, loc.line);

        match sub_span {
            None => None,
            Some(sub) => {
                let FileMapAndBytePos {fm: fm, pos: pos} = self.code_map.lookup_byte_offset(span.lo);
                let base = pos + fm.start_pos;
                Some(Span {
                    lo: base + self.code_map.lookup_byte_offset(sub.lo).pos,
                    hi: base + self.code_map.lookup_byte_offset(sub.hi).pos,
                    expn_info: None,                    
                })
            }
        }
    }

    fn snippet(&self, span: Span) -> ~str {
        match self.code_map.span_to_snippet(span) {
            Some(s) => s,
            None => ~"",
        }        
    }

    fn retokenise_span(&self, span: Span) -> StringReader {
        // sadness - we don't have spans for sub-expressions nor access to the tokens
        // so in order to get extents for the function name itself (which dxr expects)
        // we need to re-tokenise the fn definition
        let handler = diagnostic::mk_handler(~diagnostic::EmitterWriter::stderr());
        let handler = diagnostic::mk_span_handler(handler, self.code_map);

        // Note: this is a bit awful - it adds the contents of span to the end of
        // the codemap as a new filemap. This is mostly OK, but means we should
        // not iterate over the codemap. Also, any spans over the new filemap
        // are incompatible with spans over other filemaps.
        let filemap = self.code_map.new_filemap(~"<anon-dxr>",
                                                self.snippet(span));
        lexer::new_string_reader(handler, filemap)
    }

    // Re-parses a path and returns the span for the last identifier in the path
    fn span_for_last_ident(&self, span: Span) -> Option<Span> {
        let mut result = None;

        let toks = self.retokenise_span(span);
        let mut bracket_count = 0;
        loop {
            let ts = toks.next_token();
            if ts.tok == token::EOF {
                return self.make_sub_span(span, result)
            }
            if bracket_count == 0 &&
               (is_ident(&ts.tok) || is_keyword(keywords::Self, &ts.tok)) {
                result = Some(ts.sp);
            }

            if ts.tok == token::LT {
                bracket_count += 1;
            }
            if ts.tok == token::GT {
                bracket_count -= 1;
            }
            if ts.tok == token::BINOP(token::SHL) {
                bracket_count += 2;
            }
            if ts.tok == token::BINOP(token::SHR) {
                bracket_count -= 2;
            }
        }
    }

    // Return the span for the first identifier in the path.
    fn span_for_first_ident(&self, span: Span) -> Option<Span> {
        let toks = self.retokenise_span(span);
        let mut bracket_count = 0;
        loop {
            let ts = toks.next_token();
            if ts.tok == token::EOF {
                return None;
            }
            if bracket_count == 0 &&
               (is_ident(&ts.tok) || is_keyword(keywords::Self, &ts.tok)) {
                return self.make_sub_span(span, Some(ts.sp));
            }

            if ts.tok == token::LT {
                bracket_count += 1;
            }
            if ts.tok == token::GT {
                bracket_count -= 1;
            }
            if ts.tok == token::BINOP(token::SHL) {
                bracket_count += 2;
            }
            if ts.tok == token::BINOP(token::SHR) {
                bracket_count -= 2;
            }
        }
    }

    // Return the span for the last ident before a `(` or `<` and outside any
    // any brackets.
    fn sub_span_for_meth_name(&self, span: Span) -> Option<Span> {
        let toks = self.retokenise_span(span);
        let mut prev = toks.next_token();
        let mut result = None;
        let mut bracket_count = 0;
        loop {
            if prev.tok == token::EOF {
                break;
            }
            let next = toks.next_token();

            if (next.tok == token::LPAREN ||
                next.tok == token::LT) &&
               bracket_count == 0 &&
               is_ident(&prev.tok) {
                result = Some(prev.sp);
            }

            if prev.tok == token::LPAREN ||
               prev.tok == token::LT {
                bracket_count += 1;
            }
            if prev.tok == token::GT ||
               prev.tok == token::RPAREN {
                bracket_count -= 1;
            }
            if prev.tok == token::BINOP(token::SHL) {
                bracket_count += 2;
            }
            if prev.tok == token::BINOP(token::SHR) {
                bracket_count -= 2;
            }
            prev = next;
        }
        return self.make_sub_span(span, result);
    }

    // Return the span for the last ident before a `<` and outside any
    // brackets, or the last span.
    fn sub_span_for_type_name(&self, span: Span) -> Option<Span> {
        let toks = self.retokenise_span(span);
        let mut prev = toks.next_token();
        let mut result = None;
        let mut bracket_count = 0;
        loop {
            let next = toks.next_token();

            if next.tok == token::LT &&
               bracket_count == 0 &&
               is_ident(&prev.tok) {
                result = Some(prev.sp);
            }

            if prev.tok == token::LT {
                bracket_count += 1;
            }
            if prev.tok == token::GT {
                bracket_count -= 1;
            }
            if prev.tok == token::BINOP(token::SHL) {
                bracket_count += 2;
            }
            if prev.tok == token::BINOP(token::SHR) {
                bracket_count -= 2;
            }

            if next.tok == token::EOF {
                break;
            }
            prev = next;
        }
        if bracket_count != 0 {
            let loc = self.code_map.lookup_char_pos(span.lo);
            println!("Mis-counted brackets when breaking path? Parsing '{}' in {}, line {}",
                     self.snippet(span), loc.file.name, loc.line);
        }
        if is_ident(&prev.tok) && bracket_count == 0 {
            return self.make_sub_span(span, Some(prev.sp));
        }
        self.make_sub_span(span, result)
    }

    fn sub_span_before_token(&self, span: Span, tok: Token) -> Option<Span> {
        let toks = self.retokenise_span(span);
        let mut prev = toks.next_token();
        loop {
            if prev.tok == token::EOF {
                return None;
            }
            let next = toks.next_token();
            if next.tok == tok {
                return self.make_sub_span(span, Some(prev.sp));
            }
            prev = next;
        }
    }

    // Return an owned vector of the subspans of the tokens that precede
    // each occurrence of tok.
    fn all_sub_spans_before_token(&self, span: Span, tok: Token) -> ~[Span] {
        let mut sub_spans : ~[Span] = ~[];
        let toks = self.retokenise_span(span);
        let mut prev = toks.next_token();
        let mut next = toks.next_token();
        while next.tok != token::EOF {
            if next.tok == tok {
                sub_spans.push(self.make_sub_span(span, Some(prev.sp)).unwrap());
            }
            prev = next;
            next = toks.next_token();
        }
        return sub_spans;
    }

    fn sub_span_after_keyword(&self, span: Span, keyword: keywords::Keyword) -> Option<Span> {
        let toks = self.retokenise_span(span);
        loop {
            let ts = toks.next_token();
            if ts.tok == token::EOF {
                return None;
            }
            if is_keyword(keyword, &ts.tok) {
                let ts = toks.next_token();
                if ts.tok == token::EOF {
                    return None
                } else {
                    return self.make_sub_span(span, Some(ts.sp));
                }
            }
        }
    }

    // Returns a list of the spans of idents in a patch.
    // E.g., For foo::bar<x,t>::baz, we return [foo, bar, baz] (well, their spans)
    fn spans_for_path_segments(&self, path: &ast::Path) -> ~[Span] {
        // TODO we do seem to get paths with unbalanced brackets - are these bad
        // spans?

        if generated_code(path.span) {
            return ~[]
        }

        let mut result: ~[Span] = ~[];

        let toks = self.retokenise_span(path.span);
        // Only track spans for tokens outside of <...> so we don't get type vars
        let mut bracket_count = 0;
        loop {
            let ts = toks.next_token();
            if ts.tok == token::EOF {
                if bracket_count != 0 {
                    let loc = self.code_map.lookup_char_pos(path.span.lo);
                    println!("Mis-counted brackets when breaking path? Parsing '{}' in {}, line {}",
                             self.snippet(path.span), loc.file.name, loc.line);
                }
                return result
            }
            if ts.tok == token::LT {
                bracket_count += 1;
            }
            if ts.tok == token::GT {
                bracket_count -= 1;
            }
            if ts.tok == token::BINOP(token::SHL) {
                bracket_count += 2;
            }
            if ts.tok == token::BINOP(token::SHR) {
                bracket_count -= 2;
            }
            if is_ident(&ts.tok) &&
               bracket_count == 0 {
                result.push(self.make_sub_span(path.span, Some(ts.sp)).unwrap());
            }
        }
    }

    fn report_span_err(&self, kind: &str, span: Span) {
        let loc = self.code_map.lookup_char_pos(span.lo);
        println!("({}) Could not find sub_span in `{}` in {}, line {}",
                 kind, self.snippet(span), loc.file.name, loc.line);
        unsafe {
            cast::transmute_mut(self).err_count += 1;
        }
        if self.err_count > 1000 {
            fail!("span errors reached 1000, giving up");
        }
    }
}

// A map from kind of item to a tuple of
//   a vector of field names
//   whether this kind requires a span
//   whether dump_spans should dump for this kind
type FmtMap = HashMap<&'static str, (Vec<&'static str>, bool, bool)>;

struct FmtStrs {
    recorder: ~Recorder,
    span: SpanUtils,
    fmt_strs: FmtMap,
}

macro_rules! s { ($e:expr) => { format!("{}", $e) }}
macro_rules! svec {
    ($($e:expr),*) => ({
        // leading _ to allow empty construction without a warning.
        let mut _temp = ::std::vec_ng::Vec::new();
        $(_temp.push(s!($e));)*
        _temp
    })
}

impl FmtStrs {
    fn new(rec: ~Recorder, span: SpanUtils) -> FmtStrs {
        let mut result = FmtStrs {
            recorder: rec,
            span: span,
            fmt_strs: HashMap::new(),
        };

        result.fmt_strs.insert("variable", (vec!("id","name","qualname","value","scopeid"), true, true));
        result.fmt_strs.insert("enum", (vec!("id","qualname","scopeid"), true, true));
        result.fmt_strs.insert("variant", (vec!("id","name","qualname","value","scopeid"), true, true));
        result.fmt_strs.insert("variant_struct", (vec!("id","ctor_id","qualname","value","scopeid"), true, true));
        result.fmt_strs.insert("function", (vec!("id","qualname","declid","declidcrate","scopeid"), true, true));
        result.fmt_strs.insert("method_decl", (vec!("id","qualname","scopeid"), true, true));
        result.fmt_strs.insert("struct", (vec!("id","ctor_id","qualname","scopeid"), true, true));
        result.fmt_strs.insert("trait", (vec!("id","qualname","scopeid"), true, true));
        result.fmt_strs.insert("impl", (vec!("id","refid","refidcrate","scopeid"), true, true));
        result.fmt_strs.insert("module", (vec!("id","qualname","scopeid","def_file"), true, false));
        result.fmt_strs.insert("use_alias", (vec!("id","refid","refidcrate","name","scopeid"), true, true));
        result.fmt_strs.insert("extern_mod", (vec!("id","name","location","crate","scopeid"), true, true));
        result.fmt_strs.insert("inheritance",(vec!("base","basecrate","derived","derivedcrate"), false, false));
        result.fmt_strs.insert("method_call", (vec!("refid","refidcrate","declid","declidcrate","scopeid"), true, true));
        result.fmt_strs.insert("typedef", (vec!("id","qualname","value"), true, true));
        result.fmt_strs.insert("external_crate", (vec!("name","crate","file_name"), false, false));
        result.fmt_strs.insert("crate", (vec!("name"), true, false));
        macro_rules! ref_str { () => { vec!("refid","refidcrate","qualname","scopeid") }}
        result.fmt_strs.insert("fn_call", (ref_str!(), true, true));
        result.fmt_strs.insert("mod_ref", (ref_str!(), true, true));
        result.fmt_strs.insert("var_ref", (ref_str!(), true, true));
        result.fmt_strs.insert("type_ref", (ref_str!(), true, true));
        result.fmt_strs.insert("struct_ref", (ref_str!(), true, true));
        result.fmt_strs.insert("fn_ref", (ref_str!(), true, true));

        result
    }

    fn make_values_str(&self,
                       kind: &'static str,
                       fields: &Vec<&'static str>,
                       values: Vec<~str>) -> Option<~str> {
        if values.len() != fields.len() {
            println!("Mismatch between length of fields for '{}', expected '{}', found '{}'",
                     kind, fields.len(), values.len());
            return None;
        }

        let pairs = fields.iter().zip(values.iter());
        let mut strs = pairs.map(|(f, v)| format!(",{},\"{}\"", f, escape(*v)));
        Some(strs.fold(~"", |s, ss| s + ss))
    }

    fn record_without_span(&mut self,
                           kind: &'static str,
                           values: Vec<~str>) {
        if !self.fmt_strs.contains_key(&kind) {
            println!("No format string saved for '{}'", kind);
            return;            
        }

        let &(ref fields, needs_span, dump_spans) = self.fmt_strs.get(&kind);

        if needs_span {
            println!("Called record_without_span for '{}' which does requires a span", kind);
            return;            
        }
        assert!(!dump_spans);

        if self.recorder.dump_spans {
            return;
        }

        let values_str = match self.make_values_str(kind, fields, values) {
            Some(vs) => vs,
            None => return,
        };
        self.recorder.record(kind + values_str + "\n");
    }

    fn record_with_span(&mut self,
                        kind: &'static str,
                        span: Span,
                        sub_span: Span,
                        values: Vec<~str>) {
        if !self.fmt_strs.contains_key(&kind) {
            println!("No format string saved for '{}'", kind);
            return;            
        }

        let &(ref fields, needs_span, dump_spans) = self.fmt_strs.get(&kind);

        if self.recorder.dump_spans {
            if dump_spans {
                self.recorder.dump_span(self.span, kind, span, Some(sub_span));
            }
            return;
        }

        if !needs_span {
            println!("Called record_with_span for '{}' which does not require a span", kind);
            return;            
        }

        let values_str = match self.make_values_str(kind, fields, values) {
            Some(vs) => vs,
            None => return,
        };
        let head = format!("{},{}", kind, self.span.extent_str(sub_span));
        self.recorder.record(head + values_str + "\n");
    }

    fn check_and_record(&mut self,
                        kind: &'static str,
                        span: Span,
                        sub_span: Option<Span>,
                        values: Vec<~str>) {
        match sub_span {
            Some(sub_span) => self.record_with_span(kind, span, sub_span, values),
            None => self.span.report_span_err(kind, span),
        }
    }    

    fn variable_str(&mut self,
                    span: Span,
                    sub_span: Option<Span>,
                    id: NodeId,
                    name: &str,
                    value: &str) {
        // XXX getting a fully qualified name for a variable is hard because in
        // the local case they can be overridden in one block and there is no nice way
        // to refer to such a scope in english, so we just hack it by appending the
        // variable def's node id
        self.check_and_record("variable",
                              span,
                              sub_span,
                              svec!(id, name, name + "$" + id.to_str(), value, 0));
    }

    // formal parameters
    fn formal_str(&mut self,
                  span: Span,
                  sub_span: Option<Span>,
                  id: NodeId,
                  fn_name: &str,
                  name: &str) {
        self.check_and_record("variable",
                              span,
                              sub_span,
                              svec!(id, name, fn_name + "::" + name, "", 0));
    }

    // value is the initialising expression of the static if it is not mut, otherwise "".
    fn static_str(&mut self,
                  span: Span,
                  sub_span: Option<Span>,
                  id: NodeId,
                  name: &str,
                  qualname: &str,
                  value: &str,
                  scope_id: NodeId) {
        self.check_and_record("variable",
                              span,
                              sub_span,
                              svec!(id, name, qualname, value, scope_id));
    }

    fn field_str(&mut self,
                 span: Span,
                 sub_span: Option<Span>,
                 id: NodeId,
                 name: &str,
                 qualname: &str,
                 scope_id: NodeId) {
        self.check_and_record("variable",
                              span,
                              sub_span,
                              svec!(id, name, qualname, "", scope_id));
    }

    fn enum_str(&mut self,
                span: Span,
                sub_span: Option<Span>,
                id: NodeId,
                name: &str,
                scope_id: NodeId) {
        self.check_and_record("enum",
                              span,
                              sub_span,
                              svec!(id, name, scope_id));
    }

    fn tuple_variant_str(&mut self,
                         span: Span,
                         sub_span: Option<Span>,
                         id: NodeId,
                         name: &str,
                         qualname: &str,
                         val: &str,
                         scope_id: NodeId) {
        self.check_and_record("variant",
                              span,
                              sub_span,
                              svec!(id, name, qualname, val, scope_id));
    }

    fn struct_variant_str(&mut self,
                          span: Span,
                          sub_span: Option<Span>,
                          id: NodeId,
                          ctor_id: NodeId,
                          name: &str,
                          val: &str,
                          scope_id: NodeId) {
        self.check_and_record("variant_struct",
                              span,
                              sub_span,
                              svec!(id, ctor_id, name, val, scope_id));
    }

    fn fn_str(&mut self,
              span: Span,
              sub_span: Option<Span>,
              id: NodeId,
              name: &str,
              scope_id: NodeId) {
        self.check_and_record("function",
                              span,
                              sub_span,
                              svec!(id, name, "", "", scope_id));
    }

    fn method_str(&mut self,
                  span: Span,
                  sub_span: Option<Span>,
                  id: NodeId,
                  name: &str,
                  decl_id: Option<DefId>,
                  scope_id: NodeId) {
        match decl_id {
            Some(decl_id) =>
                self.check_and_record("function",
                                      span,
                                      sub_span,
                                      svec!(id, name, decl_id.node, decl_id.krate, scope_id)),
            None =>
                self.check_and_record("function",
                                      span,
                                      sub_span,
                                      svec!(id, name, "", "", scope_id)),
        }
    }

    fn method_decl_str(&mut self,
                       span: Span,
                       sub_span: Option<Span>,
                       id: NodeId,
                       name: &str,
                       scope_id: NodeId) {
        self.check_and_record("method_decl",
                              span,
                              sub_span,
                              svec!(id, name, scope_id));
    }

    fn struct_str(&mut self,
                  span: Span,   
                  sub_span: Option<Span>,
                  id: NodeId,
                  ctor_id: NodeId,
                  name: &str,
                  scope_id: NodeId) {
        self.check_and_record("struct",
                              span,
                              sub_span,
                              svec!(id, ctor_id, name, scope_id));
    }

    fn trait_str(&mut self,
                  span: Span,
                 sub_span: Option<Span>,
                 id: NodeId,
                 name: &str,
                 scope_id: NodeId) {
        self.check_and_record("trait",
                              span,
                              sub_span,
                              svec!(id, name, scope_id));
    }

    fn impl_str(&mut self,
                span: Span,
                sub_span: Option<Span>,
                id: NodeId,
                ref_id: DefId,
                scope_id: NodeId) {
        self.check_and_record("impl",
                              span,
                              sub_span,
                              svec!(id, ref_id.node, ref_id.krate, scope_id));
    }

    fn mod_str(&mut self,
               span: Span,
               sub_span: Option<Span>,
               id: NodeId,
               name: &str,
               parent: NodeId,
               filename: &str) {
        self.check_and_record("module",
                              span,
                              sub_span,
                              svec!(id, name, parent, filename));
    }

    fn use_alias_str(&mut self,
                     span: Span,
                     sub_span: Option<Span>,
                     id: NodeId,
                     mod_id: DefId,
                     name: &str,
                     parent: NodeId) {
        self.check_and_record("use_alias",
                              span,
                              sub_span,
                              svec!(id, mod_id.node, mod_id.krate, name, parent));
    }

    fn extern_mod_str(&mut self,
                      span: Span,
                      sub_span: Option<Span>,
                      id: NodeId,
                      cnum: ast::CrateNum,
                      name: &str,
                      loc: &str,
                      parent: NodeId) {
        self.check_and_record("extern_mod",
                              span,
                              sub_span,
                              svec!(id, name, loc, cnum, parent));
    }

    fn inherit_str(&mut self,
                   base_id: DefId,
                   deriv_id: NodeId) {
        // TODO add extent string here for consistency
        self.record_without_span("inheritance",
                                 svec!(base_id.node, base_id.krate, deriv_id, 0));
    }

    fn fn_call_str(&mut self,
                   span: Span,
                   sub_span: Option<Span>,
                   id: DefId,
                   scope_id:NodeId) {
        self.check_and_record("fn_call",
                              span,
                              sub_span,
                              svec!(id.node, id.krate, "", scope_id));
    }

    fn meth_call_str(&mut self,
                     span: Span,
                     sub_span: Option<Span>,
                     defid: DefId,
                     declid: Option<DefId>,
                     scope_id: NodeId) {
        match declid {
            Some(declid) =>
                self.check_and_record("method_call",
                                      span,
                                      sub_span,
                                      svec!(defid.node,
                                            defid.krate,
                                            declid.node,
                                            declid.krate,
                                            scope_id)),
            None =>
                self.check_and_record("method_call",
                                      span,
                                      sub_span,
                                      svec!(defid.node,
                                            defid.krate,
                                            "",
                                            "",
                                            scope_id)),
        }
    }

    fn sub_mod_ref_str(&mut self,
                       span: Span,
                       sub_span: Span,
                       qualname: &str,
                       parent:NodeId) {
        self.record_with_span("mod_ref",
                              span,
                              sub_span,
                              svec!(0, 0, qualname, parent));
    }

    fn typedef_str(&mut self,
                   span: Span,
                   sub_span: Option<Span>,
                   id: NodeId,
                   qualname: &str,
                   value: &str) {
        self.check_and_record("typedef",
                              span,
                              sub_span,
                              svec!(id, qualname, value));
    }

    fn crate_str(&mut self,
                 span: Span,
                 name: &str) {        
        self.record_with_span("crate",
                              span,
                              span,
                              svec!(name));
    }

    fn external_crate_str(&mut self,
                          span: Span,
                          name: &str, 
                          num: ast::CrateNum) {
        let lo_loc = self.span.code_map.lookup_char_pos(span.lo);
        self.record_without_span("external_crate",
                                 svec!(name, num, lo_loc.file.name));
    }

    fn sub_type_ref_str(&mut self,
                        span: Span,
                        sub_span: Span,
                        qualname: &str) {
        self.record_with_span("type_ref",
                              span,
                              sub_span,
                              svec!(0, 0, qualname, 0));
    }

    fn ref_str(&mut self,
               kind: &'static str,
               span: Span,
               sub_span: Option<Span>,
               id: DefId,
               scope_id: NodeId) {
        self.check_and_record(kind,
                              span,
                              sub_span,
                              svec!(id.node, id.krate, "", scope_id));
    }
}


struct DxrVisitor<'l> {
    sess: Session,
    analysis: &'l CrateAnalysis,

    collected_paths: ~[(NodeId, ast::Path, bool, &'static str)],

    span: SpanUtils,
    fmt: FmtStrs,
}

impl <'l> DxrVisitor<'l> {
    fn dump_crate_info(&mut self, name: &str, krate: &ast::Crate) {
        // the current crate
        self.fmt.crate_str(krate.span, name);

        // dump info about all the external crates referenced from this crate
        self.analysis.ty_cx.cstore.iter_crate_data(|n, cmd| {
            self.fmt.external_crate_str(krate.span, cmd.name, n);
        });
        self.fmt.recorder.record("end_external_crates\n");
    }

    // Return all non-empty prefixes of a path.
    // For each prefix, we return the span for the last segment in the prefix and
    // a str representation of the entire prefix.
    fn process_path_prefixes(&self, path: &ast::Path) -> ~[(Span, ~str)] {
        let spans = self.span.spans_for_path_segments(path);

        // XXX paths to enums seem to not match their spans - the span includes all the
        // variants too. But they seem to always be at the end, so I hope we can cope with
        // always using the first ones. So, only error out if we don't have enough spans.
        // What could go wrong...?
        if spans.len() < path.segments.len() {
            println!("Mis-calculated spans for path '{}'. Found {} spans, expected {}. Found spans:",
                     path_to_str(path), spans.len(), path.segments.len());
            for s in spans.iter() {
                let loc = self.span.code_map.lookup_char_pos(s.lo);
                println!("    '{}' in {}, line {}",
                         self.span.snippet(*s), loc.file.name, loc.line);
            }
            return ~[];
        }

        let mut result = ~[];
        for i in range(0, path.segments.len()) {
            let mut segs = path.segments.clone();
            segs.truncate(i+1);
            let sub_path = ast::Path{span: spans[i], // span for the last segment
                                     global: path.global,
                                     segments: segs};

            let qualname = path_to_str(&sub_path);
            result.push((spans[i], qualname));
        }
        result
    }

    fn write_sub_paths(&mut self, path: &ast::Path, scope_id: NodeId) {
        let sub_paths = self.process_path_prefixes(path);
        for &(ref span, ref qualname) in sub_paths.iter() {
            self.fmt.sub_mod_ref_str(path.span,
                                     *span,
                                     *qualname,
                                     scope_id);
        }        
    }

    // As write_sub_paths, but does not process the last ident in the path (assuming it
    // will be processed elsewhere).
    fn write_sub_paths_truncated(&mut self, path: &ast::Path, scope_id: NodeId) {
        let sub_paths = self.process_path_prefixes(path);
        let len = sub_paths.len();
        if len <= 1 {
            return;
        }

        let sub_paths = sub_paths.slice(0, len-1);
        for &(ref span, ref qualname) in sub_paths.iter() {
            self.fmt.sub_mod_ref_str(path.span,
                                     *span,
                                     *qualname,
                                     scope_id);
        }
    }

    // As write_sub_paths, but expects a path of the form module_path::trait::method
    // Where trait could actually be a struct too.
    fn write_sub_path_trait_truncated(&mut self, path: &ast::Path, scope_id: NodeId) {
        let sub_paths = self.process_path_prefixes(path);
        let len = sub_paths.len();
        if len <= 1 {
            return;
        }
        let sub_paths = sub_paths.slice(0, len-1);
        
        // write the trait part of the sub-path
        let (ref span, ref qualname) = sub_paths[len-2];
        self.fmt.sub_type_ref_str(path.span,
                                  *span,
                                  *qualname);

        // write the other sub-paths
        if len <= 2 {
            return;
        }
        let sub_paths = sub_paths.slice(0, len-2);
        for &(ref span, ref qualname) in sub_paths.iter() {
            self.fmt.sub_mod_ref_str(path.span,
                                     *span,
                                     *qualname,
                                     scope_id);
        }
    }

    // looks up anything, not just a type
    fn lookup_type_ref(&self, ref_id: NodeId) -> Option<DefId> {
        let def_map = self.analysis.ty_cx.def_map.borrow();
        if !def_map.get().contains_key(&ref_id) {
            println!("def_map has no key for {} in lookup_type_ref", ref_id);
            return None;
        }
        let def = *def_map.get().get(&ref_id);
        match def {
            ast::DefPrimTy(_) => None,
            _ => Some(ast_util::def_id_of_def(def)),
        }
    }

    fn lookup_def_str(&self, ref_id: NodeId) -> Option<&'static str> {
        let def_map = self.analysis.ty_cx.def_map.borrow();
        if !def_map.get().contains_key(&ref_id) {
            println!("def_map has no key for {} in lookup_type_ref", ref_id);
            return None;
        }
        let def = *def_map.get().get(&ref_id);
        match def {
            ast::DefMod(_) |
            ast::DefForeignMod(_) => Some("mod_ref"),
            ast::DefStruct(_) => Some("struct_ref"),
            ast::DefTy(_) |
            ast::DefTrait(_) => Some("type_ref"),
            ast::DefStatic(_, _) |
            ast::DefBinding(_, _) |
            ast::DefArg(_, _) |
            ast::DefLocal(_, _) |
            ast::DefVariant(_, _, _) |
            ast::DefUpvar(_, _, _, _) => Some("var_ref"),

            ast::DefFn(_, _) => Some("fn_ref"),

            ast::DefSelfTy(_) |
            ast::DefRegion(_) |
            ast::DefTyParamBinder(_) |
            ast::DefLabel(_) |
            ast::DefStaticMethod(_, _, _) |
            ast::DefTyParam(_, _) |
            ast::DefUse(_) | 
            ast::DefMethod(_, _) |
            ast::DefPrimTy(_) => {
                println!("lookup_def_str for unexpected item: {:?}", def);
                None
            },
        }
    }

    fn process_formals(&mut self, decl: @ast::FnDecl, qualname: &str, e:DxrVisitorEnv) {
        for arg in decl.inputs.iter() {
            self.collected_paths.clear();
            self.visit_pat(arg.pat, e);
            let span_utils = self.span;
            for &(id, ref p, _, _) in self.collected_paths.iter() {
                // get the span only for the name of the variable (I hope the path is only ever a
                // variable name, but who knows?)
                self.fmt.formal_str(p.span,
                                    span_utils.span_for_last_ident(p.span),
                                    id,
                                    qualname,
                                    path_to_str(p));
            }
        }
    }

    fn process_method(&mut self, method: &ast::Method, e:DxrVisitorEnv) {
        if generated_code(method.span) {
            return;
        }

        let mut scope_id = 0;
        // The qualname for a method is the trait name or name of the struct in an impl in
        // which the method is declared in followed by the method's name.
        let qualname = match ty::impl_of_method(self.analysis.ty_cx, DefId{krate:0, node:method.id}) {
            Some(impl_id) => match self.analysis.ty_cx.map.get(impl_id.node) {
                NodeItem(item) => {
                    scope_id = item.id;
                    match item.node {
                        ast::ItemImpl(_, _, ty, _) => ty_to_str(ty) + "::",
                        _ => {
                            println!("Container {} for method {} not an impl?", impl_id.node, method.id);
                            ~"???::"                                
                        },                                    
                    }
                },
                _ => {
                    println!("Could not find container {} for method {}", impl_id.node, method.id);
                    ~"???::"                                
                },
            },
            None => match ty::trait_of_method(self.analysis.ty_cx, DefId{krate:0, node:method.id}) {
                Some(def_id) => {
                    scope_id = def_id.node;
                    match self.analysis.ty_cx.map.get(def_id.node) {
                        NodeItem(_item) => self.analysis.ty_cx.map.path_to_str(def_id.node) + "::",
                        _ => {
                            println!("Could not find container {} for method {}", def_id.node, method.id);
                            ~"???::"
                        }
                    }
                },
                None => {
                    println!("Could not find container for method {}", method.id);
                    ~"???::"                                
                },
            },
        };

        let qualname = qualname + get_ident(method.ident).get();

        // record the decl for this def (if it has one)
        let decl_id = match ty::trait_method_of_method(self.analysis.ty_cx, DefId{krate:0, node:method.id}) {
            Some(def_id) => if method.id != def_id.node && def_id.node == 0 {
                Some(def_id)
            } else {
                None
            },
            None => None,
        };

        let sub_span = self.span.sub_span_after_keyword(method.span, keywords::Fn);
        self.fmt.method_str(method.span,
                            sub_span,
                            method.id,
                            qualname,
                            decl_id,
                            scope_id);

        self.process_formals(method.decl, qualname, e);

        // walk arg and return types
        for arg in method.decl.inputs.iter() {
            self.visit_ty(arg.ty, e);
        }
        self.visit_ty(method.decl.output, e);
        // walk the fn body
        self.visit_block(method.body, DxrVisitorEnv::new_nested(method.id));

        // TODO type params
    }

    fn process_struct_field_def(&mut self, field: &ast::StructField, qualname: &str, scope_id: NodeId) {
        match field.node.kind {
            ast::NamedField(ident, _) => {
                let name = get_ident(ident).get().to_owned();
                let qualname = qualname + "::" + name;
                match self.span.sub_span_before_token(field.span, token::COLON) {
                    Some(sub_span) => self.fmt.field_str(field.span,
                                                         Some(sub_span),
                                                         field.node.id,
                                                         name,
                                                         qualname,
                                                         scope_id),
                    None => println!("Could not find sub-span for field {}", qualname),
                }
            },
            _ => (),
        }
    }
}

impl<'l> Visitor<DxrVisitorEnv> for DxrVisitor<'l> {
    fn visit_item(&mut self, item:&ast::Item, e: DxrVisitorEnv) {
        if generated_code(item.span) {
            return
        }

        match item.node {
            ast::ItemFn(decl, _, _, _, body) => {
                let qualname = self.analysis.ty_cx.map.path_to_str(item.id);

                let sub_span = self.span.sub_span_after_keyword(item.span, keywords::Fn);
                self.fmt.fn_str(item.span,
                                sub_span,
                                item.id,
                                qualname,
                                e.cur_scope);

                self.process_formals(decl, qualname, e);

                // walk arg and return types
                for arg in decl.inputs.iter() {
                    self.visit_ty(arg.ty, e);
                }
                self.visit_ty(decl.output, e);

                // walk the body
                self.visit_block(body, DxrVisitorEnv::new_nested(item.id));

                // TODO walk type params
            },
            ast::ItemStatic(typ, mt, expr) => {
                let qualname = self.analysis.ty_cx.map.path_to_str(item.id);

                let value = match mt {
                    ast::MutMutable => ~"",
                    ast::MutImmutable => self.span.snippet(expr.span),
                };

                let sub_span = self.span.sub_span_after_keyword(item.span, keywords::Static);
                self.fmt.static_str(item.span,
                                    sub_span,
                                    item.id,
                                    get_ident(item.ident).get(),
                                    qualname,
                                    value,
                                    e.cur_scope);

                // walk type and init value
                self.visit_ty(typ, e);
                self.visit_expr(expr, e);
            },
            ast::ItemStruct(def, ref _g) => {
                let qualname = self.analysis.ty_cx.map.path_to_str(item.id);

                let ctor_id = match def.ctor_id {
                    Some(node_id) => node_id,
                    None => 0,
                };
                let sub_span = self.span.sub_span_after_keyword(item.span, keywords::Struct);
                self.fmt.struct_str(item.span,
                                    sub_span,
                                    item.id,
                                    ctor_id,
                                    qualname,
                                    e.cur_scope);

                // fields
                for field in def.fields.iter() {
                    self.process_struct_field_def(field, qualname, item.id);
                }

                // TODO walk type params
            },
            ast::ItemEnum(ref enum_definition, _) => {
                let qualname = self.analysis.ty_cx.map.path_to_str(item.id);
                match self.span.sub_span_after_keyword(item.span, keywords::Enum) {
                    Some(sub_span) => self.fmt.enum_str(item.span,
                                                        Some(sub_span),
                                                        item.id,
                                                        qualname,
                                                        e.cur_scope),
                    None => println!("Could not find subspan for enum {}", qualname),
                }
                for variant in enum_definition.variants.iter() {
                    let name = get_ident(variant.node.name).get().to_owned();
                    let qualname = qualname + "::" + name;
                    let val = self.span.snippet(variant.span);
                    match variant.node.kind {
                        ast::TupleVariantKind(ref args) => {
                            // first ident in span is the variant's name
                            self.fmt.tuple_variant_str(variant.span,
                                                       self.span.span_for_first_ident(variant.span),
                                                       variant.node.id,
                                                       name,
                                                       qualname,
                                                       val,
                                                       item.id);
                            for arg in args.iter() {
                                self.visit_ty(arg.ty, e);
                            }
                        }
                        ast::StructVariantKind(ref struct_def) => {
                            let ctor_id = match struct_def.ctor_id {
                                Some(node_id) => node_id,
                                None => 0,
                            };
                            self.fmt.struct_variant_str(variant.span,
                                                        self.span.span_for_first_ident(variant.span),
                                                        variant.node.id,
                                                        ctor_id,
                                                        qualname,
                                                        val,
                                                        item.id);

                            for field in struct_def.fields.iter() {
                                self.process_struct_field_def(field, qualname, variant.node.id);
                                self.visit_ty(field.node.ty, e);
                            }
                        }
                    }
                }
            },
            ast::ItemImpl(ref type_parameters, ref trait_ref, typ, ref methods) => {
                match typ.node {
                    ast::TyPath(ref path, _, id) => {
                        match self.lookup_type_ref(id) {
                            Some(id) => {
                                let sub_span = self.span.sub_span_for_type_name(path.span);
                                self.fmt.ref_str("type_ref",
                                                 path.span,
                                                 sub_span,
                                                 id,
                                                 e.cur_scope);
                                self.fmt.impl_str(path.span,
                                                  sub_span,
                                                  item.id,
                                                  id,
                                                  e.cur_scope);
                            },
                            None => ()
                        }
                    },
                    _ => self.visit_ty(typ, e),
                }

                match *trait_ref {
                    Some(ref trait_ref) => {
                        match self.lookup_type_ref(trait_ref.ref_id) {
                            Some(id) => {
                                let sub_span = self.span.sub_span_for_type_name(trait_ref.path.span);
                                self.fmt.ref_str("type_ref",
                                                 trait_ref.path.span,
                                                 sub_span,
                                                 id,
                                                 e.cur_scope);
                                self.fmt.impl_str(trait_ref.path.span,
                                                  sub_span,
                                                  item.id,
                                                  id,
                                                  e.cur_scope);
                            },
                            None => ()
                        }
                    },
                    None => (),
                }

                self.visit_generics(type_parameters, e);
                for method in methods.iter() {
                    visit::walk_method_helper(self, *method, e)
                }
            },
            ast::ItemTrait(ref generics, ref trait_refs, ref methods) => {
                let qualname = self.analysis.ty_cx.map.path_to_str(item.id);

                let sub_span = self.span.sub_span_after_keyword(item.span, keywords::Trait);
                self.fmt.trait_str(item.span,
                                   sub_span,
                                   item.id,
                                   qualname,
                                   e.cur_scope);

                // super-traits
                for trait_ref in trait_refs.iter() {
                    match self.lookup_type_ref(trait_ref.ref_id) {
                        Some(id) => {
                            let sub_span = self.span.sub_span_for_type_name(trait_ref.path.span);
                            self.fmt.ref_str("type_ref",
                                             trait_ref.path.span,
                                             sub_span,
                                             id,
                                             e.cur_scope);
                            self.fmt.inherit_str(id, item.id);
                        },
                        None => ()
                    }
                }

                // walk generics and methods
                self.visit_generics(generics, e);
                for method in methods.iter() {
                    self.visit_trait_method(method, e)
                }
            },
            ast::ItemMod(ref m) => {
                let qualname = self.analysis.ty_cx.map.path_to_str(item.id);

                // For reasons I don't understand, if there are no items in a module
                // then items is not in fact empty, but contains an empty item in the current
                // file. That is non-optimal, but we can live with it because it should be
                // pretty rare that a module has no items.
                // I'm leaving the length check just in case it changes someday, returning
                // the current file for consistency.
                let cm = self.sess.codemap;
                let filename = if m.items.len() > 0 {
                    cm.span_to_filename(m.items.get(0).span)
                } else {
                    cm.span_to_filename(item.span)
                };

                let sub_span = self.span.sub_span_after_keyword(item.span, keywords::Mod);
                self.fmt.mod_str(item.span,
                                 sub_span,
                                 item.id,
                                 qualname,
                                 e.cur_scope,
                                 filename);

                visit::walk_mod(self, m, DxrVisitorEnv::new_nested(item.id));
            },
            ast::ItemTy(ty, ref _g) => {
                let qualname = self.analysis.ty_cx.map.path_to_str(item.id);
                let value = ty_to_str(ty);
                let sub_span = self.span.sub_span_after_keyword(item.span, keywords::Type);
                self.fmt.typedef_str(item.span,
                                     sub_span,
                                     item.id,
                                     qualname,
                                     value);

                self.visit_ty(ty, e);
                //TODO type params
            },
            ast::ItemMac(_) => (),
            _ => visit::walk_item(self, item, e),
        }
    }

    // We don't actually index functions here, that is done in visit_item/ItemFn.
    // Here we just visit methods.
    fn visit_fn(&mut self, fk:&visit::FnKind, fd:&ast::FnDecl, b:&ast::Block, s:Span, n:NodeId, e:DxrVisitorEnv) {
        if generated_code(s) {
            return;
        }
        
        match *fk {
            visit::FkMethod(_, _, method) => self.process_method(method, e),
            _ => visit::walk_fn(self, fk, fd, b, s, n, e),
        }
    }

    fn visit_trait_method(&mut self, tm: &ast::TraitMethod, e: DxrVisitorEnv) {
        match *tm {
            ast::Required(ref method_type) => {
                if generated_code(method_type.span) {
                    return;
                }
        
                let mut scope_id = 0;
                let qualname = match ty::trait_of_method(self.analysis.ty_cx, DefId{krate:0, node:method_type.id}) {
                    Some(def_id) => {
                        scope_id = def_id.node;
                        match self.analysis.ty_cx.map.get(scope_id) {
                            NodeItem(_item) => self.analysis.ty_cx.map.path_to_str(scope_id) + "::",
                            _ => {
                                println!("Could not find trait {} for method {}", scope_id, method_type.id);
                                ~"???::"
                            },
                        }
                    },
                    None => {
                        println!("Could not find trait for method {}", method_type.id);
                        ~"???::"                                
                    },
                };

                let qualname = qualname + get_ident(method_type.ident).get();

                let sub_span = self.span.sub_span_after_keyword(method_type.span, keywords::Fn);
                self.fmt.method_decl_str(method_type.span,
                                         sub_span,
                                         method_type.id,
                                         qualname,
                                         scope_id);

                // walk arg and return types
                for arg in method_type.decl.inputs.iter() {
                    self.visit_ty(arg.ty, e);
                }
                self.visit_ty(method_type.decl.output, e);

                // TODO type params
            }
            ast::Provided(method) => self.process_method(method, e),
        }
    }

    fn visit_view_item(&mut self, i:&ast::ViewItem, e:DxrVisitorEnv) {
        if generated_code(i.span) {
            return
        }

        match i.node {
            ast::ViewItemUse(ref paths) => {
                for vp in paths.iter() {
                    match vp.node {
                        ast::ViewPathSimple(ident, ref path, id) => {
                            let sub_span = self.span.span_for_last_ident(vp.span);
                            let mod_id = match self.lookup_type_ref(id) {
                                Some(def_id) => {
                                    match self.lookup_def_str(id) {
                                        Some(kind) => self.fmt.ref_str(kind,
                                                                       vp.span,
                                                                       sub_span,
                                                                       def_id,
                                                                       e.cur_scope),
                                        None() => (),
                                    }
                                    def_id
                                },
                                None => DefId{node:0, krate:0},
                            };

                            // 'use' always introduces an alias, if there is not an explicit
                            // one, there is an implicit one.
                            let sub_span = match self.span.sub_span_before_token(vp.span, token::EQ) {
                                Some(sub_span) => Some(sub_span),
                                None => sub_span,
                            };

                            self.fmt.use_alias_str(vp.span,
                                                   sub_span,
                                                   id,
                                                   mod_id,
                                                   get_ident(ident).get(),
                                                   e.cur_scope);
                            self.write_sub_paths_truncated(path, e.cur_scope);
                        }
                        ast::ViewPathGlob(ref path, _) => {
                            self.write_sub_paths(path, e.cur_scope);
                        }
                        ast::ViewPathList(ref path, ref list, _) => {
                            for plid in list.iter() {
                                match self.lookup_type_ref(plid.node.id) {
                                    Some(id) => match self.lookup_def_str(plid.node.id) {
                                        Some(kind) => self.fmt.ref_str(kind,
                                                                       plid.span,
                                                                       Some(plid.span),
                                                                       id,
                                                                       e.cur_scope),
                                        None => (),
                                    },
                                    None => ()
                                }
                            }

                            self.write_sub_paths(path, e.cur_scope);
                        }
                    }
                }
            },
            ast::ViewItemExternMod(ident, ref s, id) => {
                let name = get_ident(ident).get().to_owned();
                let s = match *s {
                    Some((ref s, _)) => s.get().to_owned(),
                    None => name.to_owned(),
                };
                let sub_span = self.span.sub_span_after_keyword(i.span, keywords::Crate);
                let cstore = self.analysis.ty_cx.cstore;
                let cnum = match cstore.find_extern_mod_stmt_cnum(id) {
                    Some(cnum) => cnum,
                    None => 0,
                };
                self.fmt.extern_mod_str(i.span,
                                        sub_span,
                                        id,
                                        cnum,
                                        name,
                                        s,
                                        e.cur_scope);
            },
        }
    }

    fn visit_ty(&mut self, t:&ast::Ty, e:DxrVisitorEnv) {
        if generated_code(t.span) {
            return
        }
        
        match t.node {
            ast::TyPath(ref path, ref bounds, id) => {
                match self.lookup_type_ref(id) {
                    Some(id) => {
                        let sub_span = self.span.sub_span_for_type_name(t.span);
                        self.fmt.ref_str("type_ref",
                                         t.span,
                                         sub_span,
                                         id,
                                         e.cur_scope);
                    },
                    None => ()
                }

                self.write_sub_paths_truncated(path, e.cur_scope);

                visit::walk_path(self, path, e);
                for bounds in bounds.iter() {
                    visit::walk_ty_param_bounds(self, bounds, e)
                }
            },
            _ => visit::walk_ty(self, t, e),
        }
    }

    fn visit_expr(&mut self, ex: &ast::Expr, e: DxrVisitorEnv) {
        if generated_code(ex.span) {
            return
        }

        match ex.node {
            ast::ExprCall(_f, ref _args) => {
                // Don't need to do anything for function calls,
                // because just walking the callee path does what we want.
                visit::walk_expr(self, ex, e);
            },
            ast::ExprPath(ref path) => {
                if generated_code(path.span) {
                    return
                }

                let def_map = self.analysis.ty_cx.def_map.borrow();
                if !def_map.get().contains_key(&ex.id) {
                    println!("def_map has no key for {} in visit_expr", ex.id);
                    return;
                }
                let def = def_map.get().get(&ex.id);
                let sub_span = self.span.span_for_last_ident(ex.span);
                match *def {
                    ast::DefLocal(id, _) |
                    ast::DefArg(id, _) |
                    ast::DefUpvar(id, _, _, _) |
                    ast::DefBinding(id, _) => self.fmt.ref_str("var_ref",
                                                               ex.span,
                                                               sub_span,
                                                               DefId{node:id, krate:0},
                                                               e.cur_scope),
                    ast::DefStatic(def_id,_) => self.fmt.ref_str("var_ref",
                                                                 ex.span,
                                                                 sub_span,
                                                                 def_id,
                                                                  e.cur_scope),
                    ast::DefStruct(def_id) => self.fmt.ref_str("struct_ref",
                                                               ex.span,
                                                               sub_span,
                                                               def_id,
                                                                e.cur_scope),
                    ast::DefStaticMethod(declid, provenence, _) => {
                        let defid = if declid.krate == ast::LOCAL_CRATE {
                            let methods = self.analysis.ty_cx.methods.borrow();
                            let m = methods.get().get(&declid);
                            match provenence {
                                ast::FromTrait(def_id) =>
                                    match ty::trait_methods(self.analysis.ty_cx, def_id).iter().find(|mr| mr.ident.name == m.ident.name) {
                                            Some(mr) => mr.def_id,
                                            None => DefId{krate:0,node:0},
                                    },
                                ast::FromImpl(def_id) => {
                                    let impls = self.analysis.ty_cx.impls.borrow();
                                    match impls.get().get(&def_id).methods.iter().find(|mr| mr.ident.name == m.ident.name) {
                                        Some(mr) => mr.def_id,
                                        None => DefId{krate:0,node:0},
                                    }
                                }
                            }
                        } else {
                            DefId{krate:0,node:0}
                        };
                        self.fmt.meth_call_str(ex.span,
                                               sub_span,
                                               defid,
                                               Some(declid),
                                               e.cur_scope);
                    },
                    ast::DefFn(def_id, _) => self.fmt.fn_call_str(ex.span,
                                                                  sub_span,
                                                                  def_id,
                                                                  e.cur_scope),
                    ast::DefVariant(_, variant_id, _) => self.fmt.ref_str("var_ref",
                                                                          ex.span,
                                                                          sub_span,
                                                                          variant_id,
                                                                          e.cur_scope),
                    _ => println!("Unexpected def kind while looking up path in '{}'", self.span.snippet(ex.span)),
                }
                // modules or types in the path prefix
                match *def {
                    ast::DefStaticMethod(_, _, _) => self.write_sub_path_trait_truncated(path, e.cur_scope),
                    ast::DefLocal(_, _) |
                    ast::DefArg(_, _) |
                    ast::DefStatic(_,_) |
                    ast::DefStruct(_) |
                    ast::DefFn(_, _) => self.write_sub_paths_truncated(path, e.cur_scope),
                    _ => (),
                }

                visit::walk_path(self, path, e);
            },
            ast::ExprStruct(ref path, ref fields, base) => {
                if generated_code(path.span) {
                    return
                }

                let mut struct_def: Option<DefId> = None;
                match self.lookup_type_ref(ex.id) {
                    Some(id) => {
                        struct_def = Some(id);
                        let sub_span = self.span.span_for_last_ident(path.span);
                        self.fmt.ref_str("struct_ref",
                                         path.span,
                                         sub_span,
                                         id,
                                         e.cur_scope);
                    },
                    None => ()
                }

                self.write_sub_paths_truncated(path, e.cur_scope);

                for field in fields.iter() {
                    match struct_def {
                        Some(struct_def) => {
                            let fields = ty::lookup_struct_fields(self.analysis.ty_cx, struct_def);
                            for f in fields.iter() {
                                if generated_code(field.ident.span) {
                                    continue;
                                }
                                if f.name == field.ident.node.name {
                                    // We don't really need a sub-span here, but no harm done
                                    let sub_span = self.span.span_for_last_ident(field.ident.span);
                                    self.fmt.ref_str("var_ref",
                                                     field.ident.span,
                                                     sub_span,
                                                     f.id,
                                                     e.cur_scope);
                                }
                            }
                        },
                        _ => (),
                    }

                    self.visit_expr(field.expr, e)
                }
                visit::walk_expr_opt(self, base, e)
            },
            ast::ExprMethodCall(_, _, ref args) => {
                let method_map = self.analysis.maps.method_map.borrow();
                let method_callee = method_map.get().get(&ex.id);
                match method_callee.origin {
                    typeck::MethodStatic(def_id) => {
                        // method invoked on a struct object (not a static method)
                        let sub_span = self.span.sub_span_for_meth_name(ex.span);
                        let declid = match ty::trait_method_of_method(self.analysis.ty_cx, def_id) {
                            Some(def_id) => Some(def_id),
                            None => None
                        };
                        self.fmt.meth_call_str(ex.span,
                                               sub_span,
                                               def_id,
                                               declid,
                                               e.cur_scope);
                    }
                    typeck::MethodParam(mp) => {
                        // method invoked on a type parameter
                        let method = ty::trait_method(self.analysis.ty_cx, mp.trait_id, mp.method_num);
                        let sub_span = self.span.sub_span_for_meth_name(ex.span);
                        self.fmt.meth_call_str(ex.span,
                                               sub_span,
                                               DefId{node:0,krate:0},
                                               Some(method.def_id),
                                               e.cur_scope);
                    },
                    typeck::MethodObject(mo) => {
                        // method invoked on a trait instance
                        let method = ty::trait_method(self.analysis.ty_cx, mo.trait_id, mo.method_num);
                        let sub_span = self.span.sub_span_for_meth_name(ex.span);
                        // We don't know where object methods are defined since they are staticaly
                        // dispatched, so pass 0 as the definition id.
                        self.fmt.meth_call_str(ex.span,
                                               sub_span,
                                               DefId{node:0,krate:0},
                                               Some(method.def_id),
                                               e.cur_scope);
                    },
                }

                // walk receiver and args
                visit::walk_exprs(self, args.as_slice(), e);

                // TODO type params
            },
            ast::ExprField(sub_ex, ident, _) => {
                if generated_code(sub_ex.span) {
                    return
                }

                self.visit_expr(sub_ex, e);

                let types = self.analysis.ty_cx.node_types.borrow();
                let t = types.get().get(&(sub_ex.id as uint));
                let t = ty::type_autoderef(*t);
                let t_box = ty::get(t);
                match t_box.sty {
                    ty::ty_struct(def_id, _) => {
                        let fields = ty::lookup_struct_fields(self.analysis.ty_cx, def_id);
                        for f in fields.iter() {
                            if f.name == ident.name {
                                let sub_span = self.span.span_for_last_ident(ex.span);
                                self.fmt.ref_str("var_ref",
                                                 ex.span,
                                                 sub_span,
                                                 f.id,
                                                 e.cur_scope);
                            }
                        }
                    },
                    _ => println!("Expected struct type, but not ty_struct"),
                }
            },
            ast::ExprFnBlock(decl, body) => {
                if generated_code(body.span) {
                    return
                }

                self.process_formals(decl, "$" + ex.id.to_str(), e);

                // walk arg and return types
                for arg in decl.inputs.iter() {
                    self.visit_ty(arg.ty, e);
                }
                self.visit_ty(decl.output, e);

                // walk the body
                self.visit_block(body, DxrVisitorEnv::new_nested(ex.id));
            },
            _ => {
                visit::walk_expr(self, ex, e)
            },
        }
    }

    fn visit_mac(&mut self, _: &ast::Mac, _: DxrVisitorEnv) {
        // Just stop, macros are poison to us.
    }

    fn visit_pat(&mut self, p:&ast::Pat, e: DxrVisitorEnv) {
        if generated_code(p.span) {
            return
        }
        
        match p.node {
            ast::PatStruct(ref path, ref fields, _) => {
                self.collected_paths.push((p.id, path.clone(), false, "struct_ref"));
                visit::walk_path(self, path, e);
                let struct_def = self.lookup_type_ref(p.id);
                // the AST doesn't give us a span for the struct field, so we have
                // to figure out where it is by assuming it's the token before each colon
                let field_spans = self.span.all_sub_spans_before_token(p.span, token::COLON);
                if field_spans.len() > 0 {
                    let mut ns = 0;
                    for field in fields.iter() {
                        match struct_def {
                            Some(struct_def) => {
                                let fields = ty::lookup_struct_fields(self.analysis.ty_cx, struct_def);
                                for f in fields.iter() {
                                    if f.name == field.ident.name {
                                        self.fmt.ref_str("var_ref",
                                                         p.span,
                                                         Some(field_spans[ns]),
                                                         f.id,
                                                         e.cur_scope);
                                    }
                                }
                            },
                            _ => (),
                        }
                        self.visit_pat(field.pat, e);
                        ns += 1;
                        if ns >= field_spans.len() {
                            break;
                        }
                    }
                }
            }
            ast::PatEnum(ref path, ref children) => {
                self.collected_paths.push((p.id, path.clone(), false, "var_ref"));
                visit::walk_path(self, path, e);
                for children in children.iter() {
                    for child in children.iter() {
                        self.visit_pat(*child, e);
                    }
                }
            }
            ast::PatIdent(bm, ref path, ref optional_subpattern) => {
                let immut = match bm {
                    ast::BindByRef(mt) |
                    ast::BindByValue(mt) => {
                        match mt {
                            ast::MutMutable => false,
                            ast::MutImmutable => true,
                        }
                    }
                };
                // collect path for either visit_local or visit_arm
                self.collected_paths.push((p.id, path.clone(), immut, "var_ref"));
                match *optional_subpattern {
                    None => {}
                    Some(subpattern) => self.visit_pat(subpattern, e),
                }
            }
            _ => visit::walk_pat(self, p, e)
        }
    }

    fn visit_arm(&mut self, arm: &ast::Arm, e: DxrVisitorEnv) {
        self.collected_paths.clear();
        for pattern in arm.pats.iter() {
            // collect paths from the arm's patterns
            self.visit_pat(*pattern, e);
        }
        // process collected paths
        for &(id,ref p, ref immut, ref_kind) in self.collected_paths.iter() {
            let value = if *immut { self.span.snippet(p.span) } else { ~"" };
            let sub_span = self.span.span_for_first_ident(p.span);
            let def_map = self.analysis.ty_cx.def_map.borrow();
            if !def_map.get().contains_key(&id) {
                println!("def_map has no key for {} in visit_arm", id);
                continue;
            }
            let def = def_map.get().get(&id);
            match *def {
                ast::DefBinding(id, _) => self.fmt.variable_str(p.span,
                                                                sub_span,
                                                                id,
                                                                path_to_str(p),
                                                                value),
                ast::DefVariant(_,id,_) => self.fmt.ref_str(ref_kind,
                                                            p.span,
                                                            sub_span,
                                                            id,
                                                            e.cur_scope),
                _ => (),
            }
        }
        visit::walk_expr_opt(self, arm.guard, e);
        self.visit_expr(arm.body, e);
    }
 
    fn visit_stmt(&mut self, s:&ast::Stmt, e:DxrVisitorEnv) {
        if generated_code(s.span) {
            return
        }

        visit::walk_stmt(self, s, e)
    }

    fn visit_local(&mut self, l:&ast::Local, e: DxrVisitorEnv) {
        if generated_code(l.span) {
            return
        }

        // the local could declare multiple new vars, we must walk the pattern and collect them all
        self.collected_paths.clear();
        self.visit_pat(l.pat, e);

        let value = self.span.snippet(l.span);

        for &(id, ref p, ref immut, _) in self.collected_paths.iter() {
            let value = if *immut { value.to_owned() } else { ~"" };
            // get the span only for the name of the variable (I hope the path is only ever a
            // variable name, but who knows?)
            let sub_span = self.span.span_for_last_ident(p.span);
            // Rust uses the id of the pattern for var lookups, so we'll use it too
            self.fmt.variable_str(p.span,
                                  sub_span,
                                  id,
                                  path_to_str(p),
                                  value);
        }

        // Just walk the initialiser and type (don't want to walk the pattern again)
        self.visit_ty(l.ty, e);
        visit::walk_expr_opt(self, l.init, e);
    }
}

#[deriving(Clone)]
struct DxrVisitorEnv {
    cur_scope: NodeId,
}

impl DxrVisitorEnv {
    fn new() -> DxrVisitorEnv {
        DxrVisitorEnv{cur_scope: 0}
    }
    fn new_nested(new_mod: NodeId) -> DxrVisitorEnv {
        DxrVisitorEnv{cur_scope: new_mod}
    }
}

pub fn process_crate(sess: Session,
                     krate: &ast::Crate,
                     analysis: &CrateAnalysis,
                     odir: &Option<Path>) {
    if generated_code(krate.span) {
        return;
    }

    // TODO need to stick a random number on the end or something incase there
    // are multiple unknown crates
    let (cratename, crateid) = match attr::find_crateid(krate.attrs.as_slice()) {
        Some(crateid) => (crateid.name.clone(), crateid.to_str()),
        None => (~"unknown_crate",~"unknown_crate"),
    };

    println!("Dumping crate {} ({})", cratename, crateid);

    // find a path to dump our data to
    let mut root_path = match os::getenv("DXR_RUST_TEMP_FOLDER") {
        Some(val) => path::Path::new(val),
        None => match *odir {
            Some(ref val) => {
                let mut path = val.clone();
                path.push("dxr");
                path },
            None => path::Path::new("dxr-temp"),
        },
    };
    
    match fs::mkdir_recursive(&root_path, io::UserRWX) {
        Err(_) => {
            println!("Could not create directory {}", root_path.display());
            return;
        },
        _ => (),
    }

    {
        let disp = root_path.display();
        println!("Writing output to {}", disp);
    }

    // Create ouput file.
    root_path.push(cratename + ".csv");
    let output_file = match File::create(&root_path) {
        Ok(f) => ~f,
        Err(_) => {
            let disp = root_path.display();
            println!("Could not open {}", disp);
            return;
        }
    };
    root_path.pop();

    let mut visitor = DxrVisitor{sess: sess,
                                 analysis: analysis,
                                 collected_paths: ~[],
                                 fmt: FmtStrs::new(~Recorder{ out: output_file as ~Writer,
                                                              // TODO take this as a param or something
                                                              dump_spans: false, },
                                                   SpanUtils{ code_map: sess.codemap, err_count: 0 }),
                                 span: SpanUtils{ code_map: sess.codemap, err_count: 0 }};

    visitor.dump_crate_info(cratename, krate);

    visit::walk_crate(&mut visitor, krate, DxrVisitorEnv::new());
}
