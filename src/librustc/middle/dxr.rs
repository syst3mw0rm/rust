// TODO licence

// output data for analysis by the dxr rust plugin

use driver::driver::CrateAnalysis;
use driver::session::Session;
use middle::typeck;
use middle::typeck::lookup_def_tcx;

use syntax::ast;
use syntax::ast::*;
use syntax::ast_map::*;
use syntax::codemap::*;
use syntax::diagnostic;
use syntax::parse::lexer;
use syntax::parse::lexer::{reader, StringReader};
use syntax::parse::token::{get_ident_interner,ident_to_str,is_keyword,keywords,to_str,is_ident,EOF};
use syntax::visit;
use syntax::visit::Visitor;
use syntax::print::pprust::path_to_str;

use std::io;
use std::io::File;
use std::io::fs;
use std::os;
use std::path::Path;


struct DxrVisitor<'l> {
    sess: Session,
    analysis: &'l CrateAnalysis,

    collected_paths: ~[ast::Path],

    // output file
    out: ~Writer,
}

impl <'l> DxrVisitor<'l> {
    // standard string for extents/location
    // TODO check file name includes path
    // sub_span starts at span.lo, so we need to adjust the positions etc.
    // if sub_span is None, we don't need to adjust.
    fn extent_str(&self, span:&Span, sub_span: Option<&Span>) -> ~str {
        let cm = self.sess.codemap;
        let base_loc = cm.lookup_char_pos(span.lo);
        let base_pos: CharPos = cm.bytepos_to_local_charpos(BytePos(*span.lo - *base_loc.file.start_pos));

        let mut lo_loc = base_loc;
        let mut hi_loc = base_loc;
        let mut lo_pos: uint;
        let mut hi_pos: uint;

        match sub_span {
            Some(ss) => {
                let sub_lo = cm.lookup_char_pos(ss.lo);
                let sub_hi = cm.lookup_char_pos(ss.hi);
                lo_loc.line = base_loc.line + sub_lo.line - 1;
                lo_loc.col = CharPos(*base_loc.col + *sub_lo.col);
                hi_loc.line = base_loc.line + sub_hi.line - 1;
                hi_loc.col = CharPos(*base_loc.col + *sub_hi.col);
                lo_pos = *base_pos + *cm.bytepos_to_local_charpos(BytePos(*ss.lo - *sub_lo.file.start_pos));
                hi_pos = *base_pos + *cm.bytepos_to_local_charpos(BytePos(*ss.hi - *sub_hi.file.start_pos));
            },
            None => {
                hi_loc = cm.lookup_char_pos(span.hi);
                lo_pos = *base_pos;
                let cph: CharPos = cm.bytepos_to_local_charpos(BytePos(*span.hi - *hi_loc.file.start_pos));
                hi_pos = *cph;
            }
        }

        return format!("{},{},{},{},{},{},{}",
                       lo_loc.file.name, lo_loc.line, *lo_loc.col, lo_pos,
                       hi_loc.line, *hi_loc.col, hi_pos);
    }

    fn retokenise_span(&self, span:Span) -> @mut StringReader {
        // sadness - we don't have spans for sub-expressions nor access to the tokens
        // so in order to get extents for the function name itself (which dxr expects)
        // we need to re-tokenise the fn definition
        let cm = self.sess.codemap;
        let handler = diagnostic::mk_handler(None);
        let handler = diagnostic::mk_span_handler(handler, cm);

        let src_str = match cm.span_to_snippet(span) {
            Some(s) => s,
            None => ~"",
        };
        let filemap = cm.new_filemap(@"<anon>",
                                     src_str.to_managed());
        lexer::new_string_reader(handler, filemap)
    }

    fn span_for_name(&self, span: Span) -> Span {
        // TODO Don't highlight the whole path, just the name at the end of it
        // re-parse ex, return the span for the last identifier
        // this might not work if ex is not a path, so don't call this for a closure
        // or something

        // If we can't find a name to select, select the entire expression. This might
        // screw things up later in DXR because we might overlap with a sub-expression.
        let mut result = span;

        let mut toks = self.retokenise_span(span);
        loop {
            let ts = toks.next_token();
            if ts.tok == EOF {
                break
            }
            if is_ident(&ts.tok) {
                result = ts.sp;
            }
        }
        result
    }
}

impl<'l> Visitor<DxrVisitorEnv> for DxrVisitor<'l> {
    fn visit_item(&mut self, item:@item, e: DxrVisitorEnv) {
        match item.node {
            item_fn(_, _, _, _, _) => {
                let path = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                let mut toks = self.retokenise_span(item.span);
                let mut sub_span: Option<Span> = None;
                loop {
                    let ts = toks.next_token();
                    if ts.tok == EOF {
                        break;
                    }
                    if is_keyword(keywords::Fn, &ts.tok) {
                        // the name always comes after the 'fn' keyword
                        let ts = toks.next_token();
                        sub_span = Some(ts.sp);
                        break;
                    }
                }

                match sub_span {
                    Some(sub_span) => write!(self.out, "function,{},{},{}\n",
                                        self.extent_str(&item.span, Some(&sub_span)),
                                        path, item.id),
                    None => println("Could not find sub-span for fn name"),
                }
            }
            _ => ()
        }
        visit::walk_item(self, item, e);
    }

    fn visit_expr(&mut self, ex: @Expr, e: DxrVisitorEnv) {
        match ex.node {
            ExprCall(f, _, _) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                // TODO could be a variable, I think - what then?
                let def = def_map.get().find(&f.id);
                match def {
                    Some(d) => match *d {
                        ast::DefFn(id, _) => if id.crate == 0 {
                            let sub_span = self.span_for_name(f.span);
                            write!(self.out, "fn_call,{},{}\n",
                                   self.extent_str(&f.span, Some(&sub_span)), id.node);
                        } else {
                            // TODO
                            //println("fn from another crate");
                        },
                        // TODO warn if not index expr or closure, otherwise be quiet
                        _ => () //println("not a DefFn")
                    },
                    // TODO warn?
                    None => () //println!("Could not find {}", f.id)
                }
                //TODO - don't walk everthing (we don't want to find the fn name again), just the args
            },
            ExprPath(_) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                let def = def_map.get().find(&ex.id);
                match def {
                    Some(d) => match *d {
                        ast::DefLocal(id, _) => {
                            let sub_span = self.span_for_name(ex.span);
                            write!(self.out, "var_ref,{},{}\n",
                                   self.extent_str(&ex.span, Some(&sub_span)), id);
                        },
                        // TODO non-local vars
                        // TODO path to fns, static methods
                        _ => ()
                    },
                    // TODO warn?
                    None => () //println!("Could not find {}", ex.id)
                }
            },
            ExprMethodCall(_, _, _, _, _, _) => {
                // TODO
                /*if (!self.analysis.maps.method_map.contains_key(&ex.id)) {
                    if (self.analysis.maps.method_map.len() < 10) {
                        println!("Found expr {} {} with id {}", lo_loc.line, *lo_loc.col, ex.id);
                        //TODO is it right to use the method map? Am I using the right id to call it?
                        println("no key for method map:");
                        for (k, v) in self.analysis.maps.method_map.iter() {
                            println!("key: {},", *k);
                            match v.origin {
                                typeck::method_static(id) => println!("static {}", id.node),
                                typeck::method_param(_method_param) => println("Param"),
                                typeck::method_object(_method_object) => println("object"),
                            }
                        }
                    }
                    visit::walk_expr(self, ex, ());
                    return;
                }
                let origin = self.analysis.maps.method_map.get(&ex.id).origin;
                match origin {
                    typeck::method_static(def_id) => {
                        if (def_id.crate == LOCAL_CRATE &&
                            self.analysis.ty_cx.items.contains_key(&def_id.node)) {
                            let item = self.analysis.ty_cx.items.get(&def_id.node);
                            match *item {
                                node_item(item, path) => {
                                    let name = ident_to_str(&item.ident);
                                    println!("call to {}", name);
                                    println!("path: '{}'", path_ident_to_str(path, item.ident, get_ident_interner()));
                                }
                                //TODO
                                _ => ()
                            }
                        } else {
                            //TODO methods from another crate
                            println("non-local or no key");
                        }
                    }
                    // TODO trait methods etc,
                    _ => println("non-static method")
                }*/
            }
            _ => ()
        }
        visit::walk_expr(self, ex, e);
    }

    fn visit_pat(&mut self, p:&Pat, e: DxrVisitorEnv) {
        match p.node {
            PatIdent(_, ref path, ref optional_subpattern) => {
                self.collected_paths.push(path.clone());
                match *optional_subpattern {
                    None => {}
                    Some(subpattern) => self.visit_pat(subpattern, e),
                }
            }
            _ => visit::walk_pat(self, p, e)
        }
    }

    fn visit_local(&mut self, l:@Local, e: DxrVisitorEnv) {
        // the local could declare multiple new vars, we must walk the pattern and collect them all
        let env = DxrVisitorEnv::new();
        self.visit_pat(l.pat, env);
        for p in self.collected_paths.iter() {
            // TODO fully qual name (path + name + int) - do we need it?
            //    probably need some kind of scope info

            // get the span only for the name of the variable (I hope the path is only ever a
            // variable name, but who knows?)
            let sub_span = self.span_for_name(p.span);
            // for some reason, Rust uses the id of the pattern for var lookups, so we'll
            // use it too
            write!(self.out, "variable,{},{},{}\n",
                   self.extent_str(&p.span, Some(&sub_span)), l.pat.id, path_to_str(p, get_ident_interner()));
        }
        self.collected_paths.clear();

        // Just walk the initialiser, if it exists (don't want to walk the pattern again)
        // TODO walk the type too
        visit::walk_expr_opt(self, l.init, e);
    }

    // TODO other ways we can get a fn_decl

    // probably don't need this
    /*fn visit_fn(&mut self, fk:&fn_kind, fd:&fn_decl, b:P<Block>, s:Span, n:NodeId, _:DxrVisitorEnv) {
        //fail!("We should not walk to fn_decls, they should be processed by their owning nodes");
        let lo_loc = self.sess.codemap.lookup_char_pos(s.lo);
        let hi_loc = self.sess.codemap.lookup_char_pos(s.hi);
        // name is in the caller of this thing
        visit::walk_fn(self, fk, fd, b, s, n , ());
    }*/
}

#[deriving(Clone)]
struct DxrVisitorEnv;

impl DxrVisitorEnv {
    fn new() -> DxrVisitorEnv {
        DxrVisitorEnv
    }
}

// TODO I want the crate name, not the src_name (not sure how/if they are different)
pub fn process_crate(sess: Session,
                     crate: &ast::Crate,
                     analysis: &CrateAnalysis,
                     odir: &Option<Path>,
                     src_name: &str) {
    //TODO remove this hack once dxr-ing is optional
    if src_name != "main.rs" {
        return;
    }
    println!("Dumping crate {}", src_name);

    // find a path to dump our data to
    let mut root_path = match os::getenv("DXR_RUST_TEMP_FOLDER") {
        Some(val) => Path::new(val),
        None => match *odir {
            Some(ref val) => {
                let mut path = val.clone();
                path.push("dxr");
                path },
            None() => Path::new("~/dxr-temp"),
        },
    };
    
    fs::mkdir_recursive(&root_path, io::UserRWX);
    {
        let disp = root_path.display();
        println!("Writing output to {}", disp);
    }

    //TODO what will happen with a file in subdir? Other crates?
    let src_parts: ~[&str] = src_name.split('.').collect();
    let output_name = if src_parts.len() > 0 {
        src_parts[0].to_owned()
    } else {
        ~"output"
    };

    // create ouput file
    root_path.push(output_name + ".csv");
    let output_file = match File::create(&root_path) {
        Some(f) => ~f,
        None => {
            let disp = root_path.display();
            println!("Could not open {}", disp);
            return;
        }
    };
    root_path.pop();

    let mut visitor = DxrVisitor{sess: sess,
                                 analysis: analysis,
                                 collected_paths: ~[],
                                 out: output_file as ~Writer};
    visit::walk_crate(&mut visitor, crate, DxrVisitorEnv::new());

    // TODO need info about the crate from analysis such as exports?
}
