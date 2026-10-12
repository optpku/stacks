/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit.Basic
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit.Coherence

/-!
# Explicit reindexing comparison for categorical-pullback fibers

Compatibility aggregate for the cleavage-explicit reindexing comparison.
Focused clients can import `Explicit.Basic` for the concrete cartesian,
ambient-comparison, naturality, and conjugation API, or `Explicit.Coherence`
for the identity and composition boundaries.

The compatibility path deliberately has no declarations of its own.
-/
