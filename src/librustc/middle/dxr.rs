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

    collected_paths: ~[(NodeId, ast::Path)],

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

        return format!("file_name,{},file_line,{},file_col,{},extent_start,{},file_line_end,{},file_col_end,{},extent_end,{}",
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

        let toks = self.retokenise_span(span);
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
            item_fn(decl, _, _, _, body) => {
                let path = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                let toks = self.retokenise_span(item.span);
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
                    Some(sub_span) => write!(self.out, "function,{},qualname,{},id,{}\n",
                                        self.extent_str(&item.span, Some(&sub_span)),
                                        path, item.id),
                    None => println("Could not find sub-span for fn name"),
                }

                for arg in decl.inputs.iter() {
                    self.visit_pat(arg.pat, e);
                    for &(id, ref p) in self.collected_paths.iter() {
                        //TODO check destructing patterns
                        // TODO fully qual name (path + name + int) - do we need it - yes
                        //    probably need some kind of scope info

                        // get the span only for the name of the variable (I hope the path is only ever a
                        // variable name, but who knows?)
                        let sub_span = self.span_for_name(p.span);
                        // for some reason, Rust uses the id of the pattern for var lookups, so we'll
                        // use it too
                        write!(self.out, "variable,{},id,{},name,{},qualname,{}\n",
                               self.extent_str(&p.span, Some(&sub_span)), id, path_to_str(p, get_ident_interner()),
                               path_to_str(p, get_ident_interner()) + "$" + id.to_str());
                    }
                    self.collected_paths.clear();
                }

                // walk arg and return types
                for arg in decl.inputs.iter() {
                    self.visit_ty(arg.ty, e);
                }
                self.visit_ty(decl.output, e);

                // walk the body
                self.visit_block(body, e);

                // TODO walk type params
            },
            item_static(typ, _, expr) => {
                let toks = self.retokenise_span(item.span);
                let mut sub_span: Option<Span> = None;
                loop {
                    let ts = toks.next_token();
                    if ts.tok == EOF {
                        break;
                    }
                    if is_keyword(keywords::Static, &ts.tok) {
                        // the name always comes after the 'static' keyword
                        let ts = toks.next_token();
                        sub_span = Some(ts.sp);
                        break;
                    }
                }

                match sub_span {
                    // XXX getting a fully qualified name for a variable is hard because in
                    // the local case they can be overridden in one block and there is no nice
                    // way to refer to a scope in english, so we just hack it by appending the
                    // variable def's node id
                    Some(sub_span) => write!(self.out, "variable,{},id,{},name,{},qualname,{}\n",
                                        self.extent_str(&item.span, Some(&sub_span)),
                                        item.id, ident_to_str(&item.ident), ident_to_str(&item.ident) + "$" + item.id.to_str()),
                    None => println("Could not find sub-span for static item name"),
                }

                // walk type and init value
                self.visit_ty(typ, e);
                self.visit_expr(expr, e);
            },
            item_struct(def, ref g) => {
                // TODO refactor this out into a method
                let toks = self.retokenise_span(item.span);
                let mut sub_span: Option<Span> = None;
                loop {
                    let ts = toks.next_token();
                    if ts.tok == EOF {
                        break;
                    }
                    if is_keyword(keywords::Struct, &ts.tok) {
                        // the name always comes after the 'struct' keyword
                        let ts = toks.next_token();
                        sub_span = Some(ts.sp);
                        break;
                    }
                }

                let qualname = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                let ctor_id = match def.ctor_id {
                    Some(node_id) => node_id,
                    None => 0,
                };
                match sub_span {
                    Some(sub_span) => write!(self.out, "struct,{},id,{},ctor_id,{},qualname,{}\n",
                        self.extent_str(&item.span, Some(&sub_span)),
                        item.id, ctor_id, qualname),
                    None => println("Could not find sub-span for struct name"),
                }

                // walk the fields
                visit::walk_struct_def(self, def, item.ident, g, item.id, e);

                // TODO walk type params
            }
            _ => visit::walk_item(self, item, e),
        }
    }

    fn visit_ty(&mut self, t:&Ty, e:DxrVisitorEnv) {
        match t.node {
            ty_path(ref path, ref bounds, id) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                let def = def_map.get().find(&id);
                match def {
                    Some(d) => match *d {
                        ast::DefTy(def_id) => if def_id.crate == 0 {
                            let sub_span = self.span_for_name(t.span);
                            write!(self.out, "type_ref,{},refid,{}\n",
                                   self.extent_str(&t.span, Some(&sub_span)), def_id.node);
                        },
                        _ => (),
                    },
                    _ => (),
                }

                for bounds in bounds.iter() {
                    visit::walk_ty_param_bounds(self, bounds, e)
                }
            },
            _ => visit::walk_ty(self, t, e),
        }
    }

    fn visit_expr(&mut self, ex: @Expr, e: DxrVisitorEnv) {
        match ex.node {
            ExprCall(f, ref args, _) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                // TODO could be a variable, I think - what then?
                let def = def_map.get().find(&f.id);
                match def {
                    Some(d) => match *d {
                        ast::DefFn(id, _) => if id.crate == 0 {
                            let sub_span = self.span_for_name(f.span);
                            write!(self.out, "fn_call,{},refid,{}\n",
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

                for arg in args.iter() {
                    self.visit_expr(*arg, e);
                }
            },
            ExprPath(ref path) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                let def = def_map.get().find(&ex.id);
                match def {
                    Some(d) => match *d {
                        ast::DefLocal(id, _) |
                        ast::DefArg(id, _) => {
                            let sub_span = self.span_for_name(ex.span);
                            write!(self.out, "var_ref,{},refid,{}\n",
                                   self.extent_str(&ex.span, Some(&sub_span)), id);
                        },
                        ast::DefStatic(def_id,_) => if def_id.crate == 0 {
                            let sub_span = self.span_for_name(ex.span);
                            write!(self.out, "var_ref,{},refid,{}\n",
                                   self.extent_str(&ex.span, Some(&sub_span)), def_id.node);
                        },
                        ast::DefStruct(def_id) => if def_id.crate == 0 {
                            let sub_span = self.span_for_name(ex.span);
                            write!(self.out, "struct_ref,{},refid,{}\n",
                                   self.extent_str(&ex.span, Some(&sub_span)), def_id.node);
                        },
                        // TODO path to fns, static methods
                        _ => (), //println("Unexpected def kind"),
                    },
                    // TODO warn?
                    None => (), //println!("Could not find {}", ex.id)
                }
                visit::walk_path(self, path, e);
            },
            ExprStruct(ref path, ref fields, base) => {
                let def_map = self.analysis.ty_cx.def_map.borrow();
                let def = def_map.get().find(&ex.id);
                match def {
                    Some(d) => match *d {
                        ast::DefStruct(def_id) => if def_id.crate == 0 {
                            let sub_span = self.span_for_name(path.span);
                            write!(self.out, "struct_ref,{},refid,{}\n",
                                   self.extent_str(&path.span, Some(&sub_span)), def_id.node);
                        } else {
                            // TODO
                            //println("fn from another crate");
                        },
                        _ => () //println("not a DefStruct")
                    },
                    // TODO warn?
                    None => () //println!("Could not find {}", ex.id)
                }

                for field in fields.iter() {
                    self.visit_expr(field.expr, e)
                }
                visit::walk_expr_opt(self, base, e)
            },
            // TODO
            /*ExprMethodCall(_, _, _, _, _, _) => {
                if (!self.analysis.maps.method_map.contains_key(&ex.id)) {
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
                }
            }*/
            _ => visit::walk_expr(self, ex, e),
        }
    }

    fn visit_pat(&mut self, p:&Pat, e: DxrVisitorEnv) {
        match p.node {
            PatIdent(_, ref path, ref optional_subpattern) => {
                self.collected_paths.push((p.id, path.clone()));
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
        self.visit_pat(l.pat, e);
        for &(id,ref p) in self.collected_paths.iter() {
            // get the span only for the name of the variable (I hope the path is only ever a
            // variable name, but who knows?)
            let sub_span = self.span_for_name(p.span);
            // for some reason, Rust uses the id of the pattern for var lookups, so we'll
            // use it too
            write!(self.out, "variable,{},id,{},name,{},qualname,{}\n",
                   self.extent_str(&p.span, Some(&sub_span)), id, path_to_str(p, get_ident_interner()),
                   path_to_str(p, get_ident_interner()) + "$" + id.to_str());
        }
        self.collected_paths.clear();

        // Just walk the initialiser and type (don't want to walk the pattern again)
        self.visit_ty(l.ty, e);
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
