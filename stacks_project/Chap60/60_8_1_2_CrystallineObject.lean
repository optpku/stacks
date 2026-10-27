/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Object

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open scoped AlgebraicGeometry

universe u v w

#check (CRIS : ∀ (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme),
    Cat.{u, u + 1})

#check (CrystallineObject.of : ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) (source : Over X)
    (thickening : Scheme.{u}) (thickeningToBase : thickening ⟶ S)
    (inclusion : source.left ⟶ thickening) (ideal : thickening.IdealSheafData)
    (gamma : ∀ V : thickening.affineOpens, DividedPowers (ideal.ideal V))
    (thickening_compatible :
      ∀ (V : thickening.affineOpens) (f : Γ(thickening, V)),
        (gamma V).IsDPMorphism (gamma (thickening.affineBasicOpen f))
          (thickening.presheaf.map (homOfLE (thickening.basicOpen_le f)).op).hom)
    (isThickening : IsDividedPowerThickening thickening ideal gamma thickening_compatible)
    (inclusion_isThickening : IsThickening inclusion)
    (ideal_eq_ker : ideal = inclusion.ker)
    (source_comm : inclusion ≫ thickeningToBase = source.hom ≫ x₀ ≫ I.subschemeι),
    CrystallineObject S I γ h_compatible X x₀)

