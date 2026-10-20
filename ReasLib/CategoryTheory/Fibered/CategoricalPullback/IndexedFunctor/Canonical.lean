/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Canonical.Basic
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Canonical.Coherence
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Canonical.Hom

/-!
# Canonical indexed fiber comparison for a categorical pullback

Compatibility aggregate for the indexed comparison whose source is exactly
`fiberPseudofunctor (π₁ u p)`. The canonical owner is
`CategoricalPullback.Indexed.canonical`, with `functor`, `comparisonIso`,
and `homEquiv` datum owners. Focused clients can import the corresponding leaf.

The compatibility path deliberately has no declarations of its own.
-/
