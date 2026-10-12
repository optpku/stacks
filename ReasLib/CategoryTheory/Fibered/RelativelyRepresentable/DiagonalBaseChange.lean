/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.ProductSlice
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalBaseChange.SourceSquare
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalBaseChange.Diagonal
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalBaseChange.Comparison.OverBase

/-!
# Product-slice diagonal base change

Compatibility aggregate for the product-slice functor, its source square,
the diagonal/right-vertical comparisons, and representability transport.

New developments should import the smallest leaf for the construction or
computation layer they use.
-/

@[expose] public section
