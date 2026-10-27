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

#check (CrystallineModuleSheaf.ModuleSheaf.of : ∀ {C : Type v} [Category C]
    (thickening : C → Scheme.{u})
    (thickeningMap : ∀ {A B : C}, (A ⟶ B) → (thickening A ⟶ thickening B))
    (obj : ∀ A : C, (thickening A).Modules)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (Scheme.Modules.pullback (thickeningMap f)).obj (obj B) ⟶ obj A)
    (map_id : ∀ A : C, thickeningMap (𝟙 A) = 𝟙 (thickening A))
    (map_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      thickeningMap (f ≫ g) = thickeningMap f ≫ thickeningMap g)
    (comparison_id : ∀ A : C, comparison (𝟙 A) =
      (Scheme.Modules.pullbackCongr (map_id A)).hom.app (obj A) ≫
        (Scheme.Modules.pullbackId (thickening A)).hom.app (obj A))
    (comparison_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
      comparison (f ≫ g) =
        (Scheme.Modules.pullbackCongr (map_comp f g)).hom.app (obj D) ≫
          (Scheme.Modules.pullbackComp (thickeningMap f) (thickeningMap g)).inv.app (obj D) ≫
          (Scheme.Modules.pullback (thickeningMap f)).map (comparison g) ≫ comparison f),
    ModuleSheaf C thickening thickeningMap)

#check (CrystallineModuleSheaf.CrisModuleSheaf : ∀ (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme),
    Cat.{u + 1, u + 1})

