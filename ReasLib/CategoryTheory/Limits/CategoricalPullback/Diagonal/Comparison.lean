/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.ComparisonConstruction

/-!
# Projection comparison owners for the diagonal comparison

This module owns the two projection comparison isomorphisms for the canonical forward diagonal
comparison. Their object and component readouts are in
`CategoricalPullback.Diagonal.Computations.Comparison`; the explicit inverse and equivalence data
are in `CategoricalPullback.Diagonal.Equivalence`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory.Limits

open Functor
open scoped CategoricalPullback

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace CategoricalPullback

namespace DiagonalComparison

/-- The diagonal comparison commutes with the upper pullback projection. -/
noncomputable def fstIso (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    diagonalComparison F G H ⋙ π₁ (toDiagonal F G H) (Δₚ H) ≅
      postcompose F G H :=
  Iso.refl _

/-- The diagonal comparison commutes with the lower pullback projection. -/
noncomputable def sndIso (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    diagonalComparison F G H ⋙ π₂ (toDiagonal F G H) (Δₚ H) ≅
      toBase F G :=
  Iso.refl _

end DiagonalComparison

end CategoricalPullback

end CategoryTheory.Limits
