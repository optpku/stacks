/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Reduced

/-!
# Immersions from reduced schemes

An immersion from a reduced scheme factors through its scheme-theoretic image as an open
immersion followed by a closed immersion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical morphism from a reduced scheme to the scheme-theoretic image of an immersion
is an open immersion. -/
instance instIsOpenImmersionToImageOfIsReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) [IsImmersion h] [IsReduced Z] :
    IsOpenImmersion h.toImage := sorry

/-- An immersion from a reduced scheme factors through its scheme-theoretic image as an open
immersion followed by a closed immersion. -/
theorem exists_openImmersion_closedImmersion_factorization_of_isReduced
    {X Z : Scheme.{u}} (h : Z ⟶ X) [IsImmersion h] [IsReduced Z] :
    ∃ (Zbar : Scheme.{u}) (j : Z ⟶ Zbar) (i : Zbar ⟶ X),
      IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = h := by
  exact ⟨h.image, h.toImage, h.imageι, inferInstance, inferInstance, h.toImage_imageι⟩

end AlgebraicGeometry.Scheme.Hom
