use egg::*;
use std::ffi::{c_char, c_void, CStr, CString};

define_language! { 
    pub enum L { 
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "-" = Sub([Id; 2]),
        "/" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "sin" = Sin([Id; 1]),
        "cos" = Cos([Id; 1]),
        Symbol(Symbol),
    }
}

// Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
fn c_str_to_string(c_str: *const c_char) -> String {
    let str = unsafe { CStr::from_ptr(c_str) };
    String::from_utf8_lossy(str.to_bytes()).to_string()
}

// TODO: I think this is a memory leak right now.
fn string_to_c_str(str: String) -> *const c_char {
    let expl_c_str = CString::new(str).expect("conversion of Rust-string to C-string failed");
    expl_c_str.into_raw()
}

pub struct RewriteRule {
    name: String,
    lhs:  String,
    rhs:  String,
}

#[repr(C)]
pub struct CRewriteRule {
    name: *const c_char,
    lhs:  *const c_char,
    rhs:  *const c_char,
}

#[repr(C)]
pub struct CRewriteRuleArray {
    ptr: *const CRewriteRule,
    len: usize, 
}

impl CRewriteRuleArray {

    fn to_vec(&self) -> Vec<RewriteRule> {
        let slice = unsafe { std::slice::from_raw_parts(self.ptr, self.len) };
        slice.iter()
            .map(|rw| RewriteRule { 
                name: c_str_to_string(rw.name), 
                lhs: c_str_to_string(rw.lhs), 
                rhs: c_str_to_string(rw.rhs) 
            })
            .collect()
    }
}

#[repr(C)]
pub struct EggResult {
    success: bool,
    term: *const c_char,
    egraph: Option<Box<EGraph<L, ()>>>
}


fn make_rules(rws: Vec<RewriteRule>) -> Vec<Rewrite<L, ()>> {
    let mut rules = Vec::new();
    for r in &rws {
        let lhs_pattern: Pattern<L> = r.lhs.parse().unwrap();
        let rhs_pattern: Pattern<L> = r.rhs.parse().unwrap();
        rules.push(Rewrite::new(
            r.name.clone(),
            lhs_pattern,
            rhs_pattern
        ).unwrap());
    }
    rules
}

fn simplify_expr(target: String, rws: Vec<RewriteRule>) -> EggResult {
    let expr: RecExpr<L> = target.parse().unwrap();
    let rewrites = make_rules(rws);
    let runner = Runner::default().with_expr(&expr).run(&rewrites);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, best) = extractor.find_best(runner.roots[0]);
    let egraph = runner.egraph;
    EggResult {
        success: true,
        term: string_to_c_str(best.to_string()),
        egraph: Some(Box::new(egraph)),
    }
}


#[no_mangle]
pub extern "C" fn run_egg(target: *const c_char, rws: CRewriteRuleArray, _env: *const c_void) -> EggResult {
    let target = c_str_to_string(target);
    let rws    = rws.to_vec();
    // let egraph = EGraph::default();

    return simplify_expr(target, rws);


    // EggResult {
    //     success: true,
    //     term: string_to_c_str(format!("{:?}", target)),
    //     egraph: Some(Box::new(egraph))
    // }
}

#[no_mangle]
pub unsafe extern "C" fn query_egraph(egraph: *mut EGraph<L, ()>, query: *const c_char) -> EggResult {
    let _ = egraph.as_mut().unwrap();
    
    EggResult {
        success: true,
        term: query,
        egraph: None,
    }
}

#[no_mangle]
pub unsafe extern "C" fn free_egraph(egraph: *mut EGraph<L, ()>) {
    if !egraph.is_null() { drop(Box::from_raw(egraph)); }
}