use std::process::Command;
use std::env;

extern crate cc;

fn main() {
    let mut cc = cc::Build::new();
    cc.file("../C/ffi.c");
    
    // Get Lean compiler flags
    let bytes = Command::new("leanc")
        .args(["--print-cflags"])
        .output()
        .expect("Failed to run leanc --print-cflags")
        .stdout;
    
    let s = String::from_utf8(bytes).expect("Invalid UTF-8 from leanc");
    for flag in s.split_whitespace() {
        cc.flag(flag);
    }
    
    cc.compile("rev_ffi");
    
    // Get the workspace directory and add rpath for runtime library lookup
    let workspace = env::var("CARGO_MANIFEST_DIR").unwrap();
    let lib_path = format!("{}/../../.lake/build/lib", workspace);
    
    // Tell cargo to add rpath for the compiled library
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib_path);
    
    // Also add Lean's lib directory to rpath
    let home = env::var("HOME").unwrap();
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}/.elan/toolchains/leanprover--lean4---v4.25.0-rc2/lib/lean", home);
    
    println!("cargo:rerun-if-changed=../C/ffi.c");
}
