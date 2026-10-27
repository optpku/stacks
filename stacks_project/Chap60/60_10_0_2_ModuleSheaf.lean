/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open scoped AlgebraicGeometry

universe u v w

#check (CrystallineModuleSheaf.of : ∀ {S : Scheme.{u}} (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (obj : ∀ A : CRIS S I γ h_compatible X x₀, A.thickening.Modules)
    (comparison : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback f.thickening).obj (obj B) ⟶ obj A)
    (comparison_id : ∀ A : CRIS S I γ h_compatible X x₀,
    comparison (CrystallineObject.Hom.id A) =
      (Scheme.Modules.pullbackId A.thickening).hom.app (obj A))
    (comparison_comp : ∀ {A B C : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B) (g : CrystallineObject.Hom B C),
    comparison (CrystallineObject.Hom.comp f g) =
      (Scheme.Modules.pullbackComp f.thickening g.thickening).inv.app (obj C) ≫
        (Scheme.Modules.pullback f.thickening).map (comparison g) ≫ comparison f),
    CrystallineModuleSheaf S I γ h_compatible X x₀)

