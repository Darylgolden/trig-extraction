# trig-extraction

## Building
If you get the following error while building:
`error: Lean/TrigExtraction.lean:1:0: error loading library, libLake_shared.so: cannot open shared object file: No such file or directory`
try
```
patchelf --set-rpath $HOME/.elan/toolchains/leanprover--lean4---v4.25.0-rc2/lib/lean .lake/packages/mathlib/.lake/build/lib/libMathlib.so
patchelf --set-rpath $HOME/.elan/toolchains/leanprover--lean4---v4.25.0-rc2/lib/lean .lake/packages/importGraph/.lake/build/lib/
```
.
See [here](https://proofassistants.stackexchange.com/questions/5095/using-precompilemodules-and-mathlib-in-lakefile-causes-error-loading-library-l) and [here](https://github.com/leanprover/lean4/issues/9420).