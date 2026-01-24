use egg::*;
// mod custom_schedulers;
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
        "const" = Const([Id; 1]),
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

pub struct DirectedRewriteRule {
    name: String,
    rule: String,
}

enum Direction {
    LeftToRight,
    RightToLeft,
    Bidirectional
}

#[repr(C)]
pub struct CRewriteRule {
    name: *const c_char,
    lhs:  *const c_char,
    rhs:  *const c_char,
}

#[repr(C)]
pub struct CDirectedRewriteRule {
    name: *const c_char,
    rule: *const c_char,
}

#[repr(C)]
pub struct CRewriteRuleArray {
    ptr: *const CRewriteRule,
    len: usize, 
}

#[repr(C)]
pub struct CDirectedRewriteRuleArray {
    ptr: *const CDirectedRewriteRule,
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

impl CDirectedRewriteRuleArray {

    fn to_vec(&self) -> Vec<DirectedRewriteRule> {
        let slice = unsafe { std::slice::from_raw_parts(self.ptr, self.len) };
        slice.iter()
            .map(|directed_rw| DirectedRewriteRule {
                name: c_str_to_string(directed_rw.name),
                rule: c_str_to_string(directed_rw.rule)
            })
            .collect()
    }
}

#[repr(C)]
pub struct EggResult {
    success: bool,
    term: *const c_char,
    egraph: Option<Box<EGraph<L, ()>>>,
    explanation: *const c_char,
    log: *const c_char
}

// return pair of vec of rewrite rules and error messages instead?
fn make_rules(rws: Vec<RewriteRule>) -> (Vec<egg::Rewrite<L, ()>>, Vec<String>){
    let mut rules = Vec::new();
    let mut errors = Vec::new();
    
    for r in &rws {
        // eprintln!("Parsing {}, {}", r.lhs.parse(), r.rhs.parse());
        let lhs_pattern: Pattern<L> = match r.lhs.parse() {
            Ok(p) => p,
            Err(e) => {
                errors.push(format!("Failed to parse LHS '{}': {:?}", r.lhs, e));
                continue;
            }
        };
        let rhs_pattern: Pattern<L> = match r.rhs.parse() {
            Ok(p) => p,
            Err(e) => {
                errors.push(format!("Failed to parse RHS '{}': {:?}", r.rhs, e));
                continue;
            }
        };
        
        let name = r.name.clone();
        let name_lhs_to_rhs = name.clone() + "_lhs_to_rhs";
        let name_rhs_to_lhs = name.clone() + "_rhs_to_lhs";
        match Rewrite::new(
            name_lhs_to_rhs,
            lhs_pattern.clone(),
            rhs_pattern.clone()
        ) {
            Ok(rule) => rules.push(rule),
            Err(err) => errors.push(err)
        }
        match Rewrite::new(
            name_rhs_to_lhs,
            rhs_pattern,
            lhs_pattern
        ) {
            Ok(rule) => rules.push(rule),
            Err(err) => errors.push(err)
        }
    }
    
    (rules, errors)
}

fn make_rules_directional(directed_rws: Vec<DirectedRewriteRule>) -> (Vec<egg::Rewrite<L, ()>>, Vec<String>) {
    let mut rules= Vec::new();
    let mut errors = Vec::new();

    for r in &directed_rws {
        let name = r.name.clone();
        let rule = r.rule.clone();
        let mut direction = Option::None;
        let name_lhs_to_rhs = name.clone() + "_lhs_to_rhs";
        let name_rhs_to_lhs = name.clone() + "_rhs_to_lhs";
        let mut split_rule: Option<(&str, &str)> = Option::None;
        if rule.contains(" => ") {
            split_rule = rule.split_once(" => ");
            direction = Some(Direction::LeftToRight);
        } else if rule.contains(" <= ") {
            split_rule = rule.split_once(" <= ");
            direction = Some(Direction::RightToLeft);
        } else if rule.contains(" <=> ") {
            split_rule = rule.split_once(" <=> ");
            direction = Some(Direction::Bidirectional);
        } else {
            errors.push(format!("Failed to parse '{}'; no separator found", name));
        }
        match split_rule {
            Some((lhs, rhs)) => {
                let lhs_pattern: Pattern<L> = match lhs.parse() {
                    Ok(p) => p,
                    Err(e) => {
                        errors.push(format!("Failed to parse LHS '{}': {:?}", lhs, e));
                        continue;
                    }
                };
                let rhs_pattern: Pattern<L> = match rhs.parse() {
                    Ok(p) => p,
                    Err(e) => {
                        errors.push(format!("Failed to parse RHS '{}': {:?}", rhs, e));
                        continue;
                    }
                };
                match direction {
                    Some(Direction::LeftToRight) => 
                            match Rewrite::new(
                            name_lhs_to_rhs.clone(),
                            lhs_pattern.clone(),
                            rhs_pattern.clone()
                        ) {
                            Ok(rule) => rules.push(rule),
                            Err(err) => errors.push(err)
                        },
                    Some(Direction::RightToLeft) =>
                        match Rewrite::new(
                        name_rhs_to_lhs.clone(),
                        lhs_pattern.clone(),
                        rhs_pattern.clone()
                        ) {
                            Ok(rule) => rules.push(rule),
                            Err(err) => errors.push(err)
                        }
                    Some(Direction::Bidirectional) => {
                    match Rewrite::new(
                        name_lhs_to_rhs.clone(),
                        lhs_pattern.clone(),
                        rhs_pattern.clone()
                    ) {
                        Ok(rule) => rules.push(rule),
                        Err(err) => errors.push(err)
                    }
                    match Rewrite::new(
                        name_rhs_to_lhs.clone(),
                        rhs_pattern.clone(),
                        lhs_pattern.clone()
                    ) {
                        Ok(rule) => rules.push(rule),
                        Err(err) => errors.push(err)
                    }
                    }
                    None => {
                        errors.push(String::from("Unknown error"));
                    }
                }
                }
            None => {
                errors.push(String::from("Unknown error"));
                }
        }
    }
    (rules, errors)
}

fn simplify_expr(target: String, rws: Vec<RewriteRule>) -> Result<EggResult, String> {
    let expr: RecExpr<L> = target.parse()
        .map_err(|e| format!("Failed to parse target expression '{}': {:?}", target, e))?;
    let (rewrites, errors) = make_rules(rws);
    let mut runner = Runner::default()
                                        .with_node_limit(10000)
                                        .with_scheduler(BackoffScheduler::default().with_initial_match_limit(5))
                                        .with_explanations_enabled()
                                        .with_expr(&expr)
                                        .with_explanation_length_optimization()
                                        .run(&rewrites);

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, best) = extractor.find_best(runner.roots[0]);
    let expl = runner.explain_equivalence(&expr, &best).get_flat_string();
    let egraph = runner.egraph;
    Ok(EggResult {
        success: true,
        term: string_to_c_str(best.to_string()),
        egraph: Some(Box::new(egraph)),
        explanation: string_to_c_str(expl),
        log: string_to_c_str(errors.join("\n"))
    })
}

fn simplify_expr_directional(target: String, directed_rws: Vec<DirectedRewriteRule>) -> Result<EggResult, String> {
    let expr: RecExpr<L> = target.parse()
        .map_err(|e| format!("Failed to parse target expression '{}': {:?}", target, e))?;
    let (rewrites, errors) = make_rules_directional(directed_rws);
    let mut runner = Runner::default()
                                                        .with_node_limit(10000)
                                                        .with_explanations_enabled()
                                                        .with_expr(&expr)
                                                        .with_explanation_length_optimization()
                                                        .run(&rewrites);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, best) = extractor.find_best(runner.roots[0]);
    let expl = runner.explain_equivalence(&expr, &best).get_flat_string();
    let egraph = runner.egraph;

    Ok(EggResult {
        success: true,
        term: string_to_c_str(best.to_string()),
        egraph: Some(Box::new(egraph)),
        explanation: string_to_c_str(expl),
        log: string_to_c_str(errors.join("\n"))
    })
        
}


// need to modify egg result to accept log string
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
                explanation: string_to_c_str(String::new()),
                log: string_to_c_str(error_msg)
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
                explanation: string_to_c_str(String::new()),
                log: string_to_c_str(panic_msg)
            }
        }
    }
}

#[no_mangle]
pub extern "C" fn run_egg_directional(target: *const c_char, directed_rws: CDirectedRewriteRuleArray, _env: *const c_void) -> EggResult {
    let result = panic::catch_unwind(|| {
        let target = c_str_to_string(target);
        let directed_rws = directed_rws.to_vec();
        simplify_expr_directional(target, directed_rws)
    });
    unsafe {
        let test = c_str_to_string(rs_transfer_string(string_to_c_str(String::from("meow"))));
        println!("{test}");
    }
    match result {
        Ok(Ok(egg_result)) => egg_result,
        Ok(Err(error_msg)) => {
            EggResult {
                success: false,
                term: string_to_c_str(String::new()),
                egraph: None,
                explanation: string_to_c_str(String::new()),
                log: string_to_c_str(error_msg)
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
                explanation: string_to_c_str(String::new()),
                log: string_to_c_str(panic_msg)
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
                explanation: string_to_c_str(String::new()),
                log: string_to_c_str(String::new())
            }
        }
        Ok(Err(error_msg)) => {
            EggResult {
                success: false,
                term: string_to_c_str(String::new()),
                egraph: None,
                explanation: string_to_c_str(format!("Error: {}", error_msg)),
                log: string_to_c_str(String::new())
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
                explanation: string_to_c_str(String::new()),
                log: string_to_c_str(panic_msg)
            }
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn free_egraph(egraph: *mut EGraph<L, ()>) {
    if !egraph.is_null() { drop(Box::from_raw(egraph)); }
}

extern "C" {
    fn rs_transfer_string(name: *const c_char) -> *const c_char;
}