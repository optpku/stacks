/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.Iteration.Center
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Cosimplicial
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Simplicial

/-!
# Iterated endofunctors

Compatibility facade for the reusable iteration API. Downstream files should import the
narrowest of `Core`, `Positive`, `Center`, `Cosimplicial`, and `Simplicial`.
-/
