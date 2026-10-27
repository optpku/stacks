/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Site


open AlgebraicGeometry CategoryTheory

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

#check (AlgebraicGeometry.Scheme.Crystalline.chaoticInclusion S I γ h_compatible X x₀ : chaoticSite S I γ h_compatible X x₀ ⥤
      smallCrystallineSite S I γ h_compatible X x₀)

end AlgebraicGeometry.Scheme.Crystalline
