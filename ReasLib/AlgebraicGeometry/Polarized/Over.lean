/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BaseChange

/-!
# Polarized families over an algebraic space

Polarized proper schemes whose base schemes map to an algebraic space form a
category fibred in groupoids over schemes over `Spec ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The functor sending a polarized family with a base map to `B` to its base
scheme, viewed over `Spec ℤ`. -/
def polarizedOver.p (B : AlgebraicSpace specZ) :
    AlgebraicSpace.categoryBaseChange Polarized.p B ⥤ Over specZ :=
  CostructuredArrow.proj
    (Polarized.p ⋙ AlgebraicSpace.baseChangeToOverSpecZ ⋙
      AlgebraicSpace.categoryBaseChange.ofOverFunctor) B ⋙
    Polarized.p ⋙ AlgebraicSpace.baseChangeToOverSpecZ

/-- The base-scheme functor is the costructured-arrow projection followed by
the polarized base-scheme functor and the canonical functor to `Sch / Spec ℤ`. -/
theorem polarizedOver.p_eq (B : AlgebraicSpace specZ) :
    polarizedOver.p B =
      CostructuredArrow.proj
        (Polarized.p ⋙ AlgebraicSpace.baseChangeToOverSpecZ ⋙
          AlgebraicSpace.categoryBaseChange.ofOverFunctor) B ⋙
        Polarized.p ⋙ AlgebraicSpace.baseChangeToOverSpecZ :=
  rfl

/-- Polarized families with a base map to `B` are fibred in groupoids over
schemes over `Spec ℤ`. -/
instance polarizedOver.instIsFiberedInGroupoids (B : AlgebraicSpace specZ) :
    Functor.IsFibered.InGroupoids (polarizedOver.p B) :=
  sorry

/-- Polarized families with a base map to `B`, bundled as a category fibred in
groupoids over schemes over `Spec ℤ`, with Hom-universe `u`. -/
def polarizedOver.toGroupoids (B : AlgebraicSpace specZ) : GroupoidsOver specZ :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u}
    (polarizedOver.p B)

/-- The total category of the bundled groupoid fibration is the category of
polarized families whose base schemes map to `B`. -/
theorem polarizedOver.toGroupoids_total (B : AlgebraicSpace specZ) :
    (polarizedOver.toGroupoids B).total =
      AlgebraicSpace.categoryBaseChange Polarized.p B :=
  rfl

end AlgebraicGeometry.Polarized
