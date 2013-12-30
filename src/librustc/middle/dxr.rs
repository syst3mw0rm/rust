// TODO licence

// output data for analysis by the dxr rust plugin

//TODO order these
use driver::session::Session;
use driver::driver::CrateAnalysis;
use middle::typeck;
use middle::typeck::lookup_def_tcx;

use syntax::ast;
use syntax::ast::*;
use syntax::ast_map::*;
use syntax::visit;
use syntax::visit::Visitor;
use syntax::visit::fn_kind;
use syntax::parse::token::get_ident_interner;
use syntax::parse::token::ident_to_str;
use syntax::codemap::{Span, Spanned};

use std::os;
use std::io;
use std::io::File;
use std::path::Path;
use std::io::fs;


struct DxrVisitor<'l> {
    sess: Session,
    analysis: &'l CrateAnalysis,

    // output files
    f_fn_calls: ~Writer,
    f_fn_defs: ~Writer,
}

impl<'l> Visitor<()> for DxrVisitor<'l> {
    fn visit_item(&mut self, item:@item, _:()) {
        let lo_loc = self.sess.codemap.lookup_char_pos(item.span.lo);
        let hi_loc = self.sess.codemap.lookup_char_pos(item.span.hi);
        let cp: syntax::codemap::CharPos = self.sess.codemap.bytepos_to_local_charpos(item.span.lo);
        let lo_extent: uint = cp.to_uint();
        let hi_extent = self.sess.codemap.bytepos_to_local_charpos(item.span.hi).to_uint();

        match item.node {
            item_fn(_, _, _, _, _) => {
                // TODO check file name includes path
                let path = match *self.analysis.ty_cx.items.get(&item.id) {
                    node_item(_, path) => path_ident_to_str(path, item.ident, get_ident_interner()),
                    _ => ~""
                };

                write!(self.f_fn_defs, "{},{},{},{},{},{},{},{},{}\n",
                                        lo_loc.file.name, lo_loc.line, *lo_loc.col, lo_extent,
                                        hi_loc.line, *hi_loc.col, hi_extent,
                                        path, item.id);
                
            }
            _ => ()
        }
        visit::walk_item(self, item, ())
    }

    fn visit_expr(&mut self, ex:@Expr, _:()) {
        let lo_loc = self.sess.codemap.lookup_char_pos(ex.span.lo);
        let hi_loc = self.sess.codemap.lookup_char_pos(ex.span.hi);
        let lo_extent = self.sess.codemap.bytepos_to_local_charpos(ex.span.lo).to_uint();
        let hi_extent = self.sess.codemap.bytepos_to_local_charpos(ex.span.hi).to_uint();

        match ex.node {
            ExprCall(f, _, _) => {
                let def = self.analysis.ty_cx.def_map.find(&f.id);
                match def {
                    Some(d) => match *d {
                        ast::DefFn(id, _) => if id.crate == 0 {
                            write!(self.f_fn_calls, "{},{},{},{},{},{},{},{}\n",
                                                    lo_loc.file.name, lo_loc.line, *lo_loc.col, lo_extent,
                                                    hi_loc.line, *hi_loc.col, hi_extent,
                                                    id.node);
                        } else {
                            // TODO
                            //println("fn from another crate");
                        },
                        // TODO warn if not index expr or closure, otherwise be quiet
                        _ => () //println("not a DefFn")
                    },
                    None => () //println!("Could not find {}", f.id)
                }
            }
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
        visit::walk_expr(self, ex, ());
    }

    // TODO other ways we can get a fn_decl

    // probably don't need this
    /*fn visit_fn(&mut self, fk:&fn_kind, fd:&fn_decl, b:P<Block>, s:Span, n:NodeId, _:()) {
        //fail!("We should not walk to fn_decls, they should be processed by their owning nodes");
        let lo_loc = self.sess.codemap.lookup_char_pos(s.lo);
        let hi_loc = self.sess.codemap.lookup_char_pos(s.hi);
        // name is in the caller of this thing
        visit::walk_fn(self, fk, fd, b, s, n , ());
    }*/
}

// TODO I want the crate name, not the src_name (not sure how/if they are different)
pub fn process_crate(sess: Session,
                     crate: &ast::Crate,
                     analysis: &CrateAnalysis,
                     odir: &Option<Path>,
                     src_name: @str) {
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
    
    let src_parts: ~[&str] = src_name.split('.').collect();
    if src_parts.len() > 0 {
        root_path.push(src_parts[0]);
    }

    fs::mkdir_recursive(&root_path, io::UserRWX);

    {
        let disp = root_path.display();
        println!("Writing output to {}", disp);
    }

    // create ouput files
    //TODO refactor
    root_path.push("fn_defs.csv");
    let mut f_fn_defs = match File::create(&root_path) {
        Some(f) => ~f,
        None => {
            let disp = root_path.display();
            println!("Could not open {}", disp);
            return;
        }
    };
    root_path.pop();

    root_path.push("fn_calls.csv");
    let mut f_fn_calls = match File::create(&root_path) {
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
                                 f_fn_defs: f_fn_defs as ~Writer,
                                 f_fn_calls: f_fn_calls as ~Writer,};
    visit::walk_crate(&mut visitor, crate, ());

    // TODO need info about the crate from analysis such as exports
}
