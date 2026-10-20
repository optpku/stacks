/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Bilimit
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilimit property of the diagonal pullback square

This module identifies the explicit diagonal comparison square with a categorical
pseudo-pullback bilimit.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v u

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable {D : Type (max u v)} [Category.{v} D]

namespace CategoricalPullback.diagonalSquareOver

/-- The canonical square comparing a categorical pullback before and after postcomposition is a
bicategorical pseudo-pullback bilimit. -/
@[stacks 04Z1 "postcomposition diagonal pullback bilimit"]
instance isBilimit
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (diagonalSquareOver F G H).IsBilimit := sorry
/- Proof strategy: apply `CatCommSqOver.isBilimit_iff_comparisonIsEquivalence`. The comparison
functor is `diagonalComparison F G H`, whose explicit equivalence is constructed in
`DiagonalComparison.equivalence`. -/

end CategoricalPullback.diagonalSquareOver

end CategoryTheory.Limits
