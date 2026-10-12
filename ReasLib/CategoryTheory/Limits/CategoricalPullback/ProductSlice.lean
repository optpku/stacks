/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.Equivalence
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.Computations

/-!
# Categorical pullbacks of slice projections

Compatibility aggregate for the canonical equivalence between the categorical pullback of two
slice projections and the slice over their product.  Focused consumers should import `Basic`,
`Equivalence`, or `Computations` according to the layer they use.
-/
