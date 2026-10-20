/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Over
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- For the zero scheme `Z(s)` of a section, Gysin pullback after proper pushforward sends
`α` to `c₁(ℒ|_Z(s)) ∩ α`. -/
theorem gysin_map_eq_firstChernClassCap
    {S : Scheme.{u}} [UniversallyCatenary S] (X : Over S) [LocallyOfFiniteType X.hom]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (k : ℤ) (α : RelativeChow δ (Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom)) k) :
    gysin δ X ℒ s k
        (map δ (Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom)) X
          (Over.homMk (Scheme.zeroSchemeι ℒ s) :
            Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom) ⟶ X) k α) =
      firstChernClassCap δ (Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom))
        ((Scheme.Modules.pullback
          ((Over.homMk (Scheme.zeroSchemeι ℒ s) :
            Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom) ⟶ X).left)).obj ℒ) k α := sorry

end AlgebraicGeometry.ChowGroup
