/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Restriction of scalars as a fibre of relative morphisms

Restriction of scalars is the fibre of postcomposition along the identity section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

variable {S : Scheme.{u}} {X Z B : AlgebraicSpace S}

/-- A lift over `Z`, transported to the categorical pullback, lies over `B`. -/
theorem toRelativeHom_w (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Pair f g T) :
    ((fiberPullbackIso g p.base).inv ≫ p.lift) ≫ (f ≫ g) =
      pullback.fst p.base g ≫ p.base := sorry

/-- Forget the triangle over `Z` to obtain a relative morphism over `B`. -/
def toRelativeHomPoint (f : X ⟶ Z) (g : Z ⟶ B) {T : Over S} (p : Pair f g T) :
    RelativeHom.Pair g (f ≫ g) T :=
  RelativeHom.mk p.base (RelativeHom.BaseChangeMorphism.ofMap
    ((fiberPullbackIso g p.base).inv ≫ p.lift) (toRelativeHom_w f g p))

/-- Forgetting the triangle over `Z` commutes with restriction to test schemes. -/
theorem toRelativeHom_naturality (f : X ⟶ Z) (g : Z ⟶ B)
    {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (restrictionOfScalars f g).map φ ≫ TypeCat.ofHom (toRelativeHomPoint f g) =
      TypeCat.ofHom (toRelativeHomPoint f g) ≫ (RelativeHom.presheaf g (f ≫ g)).map φ :=
  sorry

/-- The canonical forgetful morphism from restriction of scalars to relative morphisms. -/
def toRelativeHom (f : X ⟶ Z) (g : Z ⟶ B) :
    sheaf f g ⟶ RelativeHom.sheaf g (f ≫ g) :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom (toRelativeHomPoint f g)
      naturality := fun _ _ φ ↦ toRelativeHom_naturality f g φ }

/-- Components of the forgetful morphism are obtained by forgetting the triangle over `Z`. -/
theorem toRelativeHom_app (f : X ⟶ Z) (g : Z ⟶ B) (T : (Over S)ᵒᵖ) :
    (toRelativeHom f g).hom.app T =
      TypeCat.ofHom fun (p : Pair f g T.unop) ↦ toRelativeHomPoint f g p := rfl

/-- Restriction of scalars is the fibre of postcomposition along the identity section
in the category of fppf sheaves. -/
theorem isPullback (f : X ⟶ Z) (g : Z ⟶ B) :
    IsPullback (toRelativeHom f g) (toBase f g) (RelativeHom.postcomp f g)
      (RelativeHom.idSection g) := sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
