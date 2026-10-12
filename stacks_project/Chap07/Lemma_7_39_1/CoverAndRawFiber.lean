/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.CategoryTheory.Sites.Family.Sheaf.Refinement

/-!
# Compatibility import for cover pullback and separatedness

Componentwise base change of covering families is owned by
`SemiRepresentableFamily.Over.baseChange_toSieve_mem`; separatedness gives
the reusable restriction-injectivity API in
`ReasLib.CategoryTheory.Sites.Family.Sheaf.Refinement`.  This legacy Chapter 7
path contains no independent data.
-/

@[expose] public section
