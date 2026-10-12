/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Computations
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Comparison
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Comparison.Computations
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Diagonal.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Diagonal.Equivalence

/-!
# Product-slice right-vertical API

Compatibility aggregate for the generic right-vertical functor, its computation and comparison
formulas, and the product-slice diagonal equivalence. Focused downstream files should import the
smallest leaf needed for their construction.
-/
