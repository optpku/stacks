/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import stacks_project.Chap60.«60_8_1_2_CrystallineObject»

@[expose] public section

open AlgebraicGeometry CategoryTheory

/-- A crystalline module sheaf assigns a module sheaf to each crystalline thickening and a
comparison morphism to every morphism of crystalline-site objects. -/
structure CrystallineModuleSheaf.{u}
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) where
  /-- The module sheaf on the thickening of a crystalline-site object. -/
  obj : ∀ A : CRIS S I γ h_compatible X x₀, A.thickening.Modules
  /-- The comparison morphism induced by a morphism of crystalline-site objects. -/
  comparison : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
    (Scheme.Modules.pullback f.thickening).obj (obj B) ⟶ obj A

/-- Construct a crystalline module sheaf from its objectwise module sheaves and comparison family. -/
def CrystallineModuleSheaf.of
    {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (obj : ∀ A : CRIS S I γ h_compatible X x₀, A.thickening.Modules)
    (comparison : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback f.thickening).obj (obj B) ⟶ obj A) :
    CrystallineModuleSheaf S I γ h_compatible X x₀ :=
  { obj, comparison }
