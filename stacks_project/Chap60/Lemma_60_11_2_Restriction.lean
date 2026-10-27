/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open scoped AlgebraicGeometry

universe u v w

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

#check (CrystallineModuleSheaf.restrict : ∀ (F : SheafOfModules (structureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))),
    ModuleSheaf (RelativeCRIS S I γ h_compatible X x₀) (fun A => A.1.thickening) (fun {A B} (f : A ⟶ B) => f.thickening))

#check (CrystallineModuleSheaf.CrisModuleSheaf.restrict : ∀ (F : SheafOfModules (smallStructureSheaf (S := S) (I := I) (γ := γ)
      (h_compatible := h_compatible) (X := X) (x₀ := x₀))),
    CrisModuleSheaf S I γ h_compatible X x₀)

