/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Site

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- The functor sending a relative crystalline object to its thickening scheme. -/
def thickeningFunctor
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :
    RelativeCRIS S I γ h_compatible X x₀ ⥤ Scheme.{u} where
  obj := fun A ↦ A.1.thickening
  map := fun f ↦ f.thickening
  map_id := fun _ ↦ rfl
  map_comp := fun _ _ ↦ rfl

/-- The functor sending a small crystalline object to its thickening scheme. -/
def smallThickeningFunctor
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :
    smallCrystallineSite S I γ h_compatible X x₀ ⥤ Scheme.{u} where
  obj := fun A ↦ A.obj.1.thickening
  map := fun f ↦ f.hom.thickening
  map_id := fun _ ↦ rfl
  map_comp := fun _ _ ↦ rfl

end AlgebraicGeometry.Scheme.Crystalline
