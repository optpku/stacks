/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor

/-!
# Standard-fiber reindexing from a cleavage

This is the stable umbrella for cleavage-induced reindexing. The implementation is split by
dependency layer:

* `Reindex.Lift` owns the chosen object and cartesian arrow;
* `Reindex.Factorization` owns universal and vertical-cartesian factors;
* `Reindex.Functor` owns the morphism action, functor, and notation.

Import a leaf directly when only one layer is needed.
-/
