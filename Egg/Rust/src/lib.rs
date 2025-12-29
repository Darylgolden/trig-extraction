use egg::*;
use std::ffi::{c_char, c_void, CStr, CString};
use std::panic;

define_language! { 
    pub enum L { 
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "-" = Sub([Id; 2]),
        "/" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "neg" = Neg([Id; 1]),
        "inv" = Inv([Id; 1]),
        "sin" = Sin([Id; 1]),
        "cos" = Cos([Id; 1]),
        "tan" = Tan([Id; 1]),
        "sqrt" = Sqrt([Id; 1]),
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
    egraph: Option<Box<EGraph<L, ()>>>,
    explanation: *const c_char
}


fn make_rules(rws: Vec<RewriteRule>) -> Result<Vec<Rewrite<L, ()>>, String> {
    let mut rules = Vec::new();
    for r in &rws {
        let lhs_pattern: Pattern<L> = r.lhs.parse()
            .map_err(|e| format!("Failed to parse LHS '{}': {:?}", r.lhs, e))?;
        let rhs_pattern: Pattern<L> = r.rhs.parse()
            .map_err(|e| format!("Failed to parse RHS '{}': {:?}", r.rhs, e))?;
        let name = r.name.clone();
        let name_lhs_to_rhs = name.clone() + "_lhs_to_rhs";
        rules.push(Rewrite::new(
            name_lhs_to_rhs.clone(),
            lhs_pattern.clone(),
            rhs_pattern.clone()
        ).map_err(|e| format!("Failed to create rewrite rule '{}': {:?}", name_lhs_to_rhs, e))?);
        let name_rhs_to_lhs = name.clone() + "_rhs_to_lhs";
        rules.push(Rewrite::new(
            name_rhs_to_lhs.clone(),
            rhs_pattern,
            lhs_pattern
        ).map_err(|e| format!("Failed to create rewrite rule '{}': {:?}", name_rhs_to_lhs, e))?);
    }
    Ok(rules)
}

fn simplify_expr(target: String, rws: Vec<RewriteRule>) -> Result<EggResult, String> {
    let expr: RecExpr<L> = target.parse()
        .map_err(|e| format!("Failed to parse target expression '{}': {:?}", target, e))?;
    let rewrites = make_rules(rws)?;
    let mut runner = Runner::default().with_explanations_enabled().with_expr(&expr).run(&rewrites);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, best) = extractor.find_best(runner.roots[0]);
    let expl = runner.explain_equivalence(&expr, &best).get_flat_string();
    let egraph = runner.egraph;
    Ok(EggResult {
        success: true,
        term: string_to_c_str(best.to_string()),
        egraph: Some(Box::new(egraph)),
        explanation: string_to_c_str(expl)
    })
}


#[no_mangle]
pub extern "C" fn run_egg(target: *const c_char, rws: CRewriteRuleArray, _env: *const c_void) -> EggResult {
    let result = panic::catch_unwind(|| {
        let target = c_str_to_string(target);
        let rws    = rws.to_vec();
        simplify_expr(target, rws)
    });

    match result {
        Ok(Ok(egg_result)) => egg_result,
        Ok(Err(error_msg)) => {
            EggResult {
                success: false,
                term: string_to_c_str(String::new()),
                egraph: None,
                explanation: string_to_c_str(format!("Error: {}", error_msg))
            }
        }
        Err(panic_info) => {
            let panic_msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                format!("Panic: {}", s)
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                format!("Panic: {}", s)
            } else {
                "Panic: unknown error".to_string()
            };
            EggResult {
                success: false,
                term: string_to_c_str(String::new()),
                egraph: None,
                explanation: string_to_c_str(panic_msg)
            }
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn query_egraph(egraph: *mut EGraph<L, ()>, query: *const c_char) -> EggResult {
    let result = panic::catch_unwind(|| {
        if egraph.is_null() {
            return Err("Null egraph pointer".to_string());
        }
        let _graph = egraph.as_mut().ok_or("Invalid egraph pointer")?;
        Ok(())
    });

    match result {
        Ok(Ok(())) => {
            EggResult {
                success: true,
                term: query,
                egraph: None,
                explanation: string_to_c_str("".to_string())
            }
        }
        Ok(Err(error_msg)) => {
            EggResult {
                success: false,
                term: string_to_c_str(String::new()),
                egraph: None,
                explanation: string_to_c_str(format!("Error: {}", error_msg))
            }
        }
        Err(panic_info) => {
            let panic_msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                format!("Panic: {}", s)
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                format!("Panic: {}", s)
            } else {
                "Panic: unknown error".to_string()
            };
            EggResult {
                success: false,
                term: string_to_c_str(String::new()),
                egraph: None,
                explanation: string_to_c_str(panic_msg)
            }
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn free_egraph(egraph: *mut EGraph<L, ()>) {
    if !egraph.is_null() { drop(Box::from_raw(egraph)); }
}