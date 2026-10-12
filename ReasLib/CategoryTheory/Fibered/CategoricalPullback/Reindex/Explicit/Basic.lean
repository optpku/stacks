/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit.Construction
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit.Naturality

/-!
# Explicit reindexing comparison for categorical-pullback fibers

Compatibility aggregate for the cleavage-explicit reindexing comparison.
Focused clients can import `Explicit.Construction` for the concrete
cartesian comparison or `Explicit.Naturality` for its naturality and
conjugation formulas.

The compatibility path deliberately has no declarations of its own.
-/
