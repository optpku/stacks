/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.ExceptionalDivisor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Universal property of blowups of algebraic spaces

The blowup along a closed subspace is final among spaces over the ambient space
on which the inverse image of the center is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Blowup

/-- The full subcategory of spaces over `X` whose inverse image of the closed
subspace `Z` is an effective Cartier divisor. -/
abbrev effectiveCartierPullbackOverCategory {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :=
  ObjectProperty.FullSubcategory fun Y : Over X ↦
    IsEffectiveCartierDivisor (Z.inverseImageSubspace Y.hom).ι

namespace effectiveCartierPullbackOverCategory

/-- The inverse image of the center under its blowup is an effective Cartier divisor. -/
theorem inverseImage_isEffectiveCartier {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    IsEffectiveCartierDivisor (Z.inverseImageSubspace (Blowup.alongHom Z π)).ι :=
  sorry

/-- The blowup along `Z`, as an object of the full subcategory of spaces over `X`
whose inverse image of `Z` is an effective Cartier divisor. -/
def blowupObject {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) : effectiveCartierPullbackOverCategory Z where
  obj := Over.mk (Blowup.alongHom Z π)
  property := inverseImage_isEffectiveCartier Z π

/-- The underlying slice object of the blowup object is its structure morphism. -/
theorem blowupObject_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    (blowupObject Z π).obj = Over.mk (Blowup.alongHom Z π) :=
  rfl

/-- The structure morphism of the blowup object is the blowup morphism. -/
theorem blowupObject_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    (blowupObject Z π).obj.hom = Blowup.alongHom Z π :=
  rfl

/-- The blowup object has effective Cartier inverse image of its center. -/
theorem blowupObject_property {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) :
    IsEffectiveCartierDivisor (Z.inverseImageSubspace (blowupObject Z π).obj.hom).ι :=
  (blowupObject Z π).property

/-- A morphism whose inverse image of the center is an effective Cartier divisor
factors uniquely through the blowup morphism. -/
theorem existsUnique_lift {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Z : ClosedSubspace X} (π : along Z) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (hg : IsEffectiveCartierDivisor (Z.inverseImageSubspace g).ι) :
    ExistsUnique fun h : Y ⟶ Blowup.alongSpace Z π ↦ h ≫ Blowup.alongHom Z π = g :=
  sorry

/-- Every space over `X` with effective Cartier inverse image of `Z` admits a
unique morphism over `X` to the blowup along `Z`. -/
theorem existsUnique_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z)
    (Y : effectiveCartierPullbackOverCategory Z) :
    ExistsUnique fun f : Y ⟶ blowupObject Z π ↦
      f.hom.left ≫ Blowup.alongHom Z π = Y.obj.hom :=
  sorry

/-- A morphism to the blowup object in the full subcategory commutes with the
structure morphisms to `X`. -/
theorem hom_w {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z)
    {Y : effectiveCartierPullbackOverCategory Z}
    (f : Y ⟶ blowupObject Z π) :
    f.hom.left ≫ Blowup.alongHom Z π = Y.obj.hom :=
  Over.w f.hom

end effectiveCartierPullbackOverCategory

end AlgebraicGeometry.AlgebraicSpace
