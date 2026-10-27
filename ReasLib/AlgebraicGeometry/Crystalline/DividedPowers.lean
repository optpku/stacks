/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import ReasLib.AlgebraicGeometry.DividedPowers.Scheme.Morphism

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace CrystallineObject

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {hc : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- The divided-power scheme carried by a crystalline thickening has its actual
defining ideal and divided-power operations. -/
def dividedPowerScheme (A : CrystallineObject S I γ hc X x₀) : DividedPowerScheme.{u} where
  scheme := A.thickening
  ideal := A.ideal
  quasiCoherent := sorry
  dividedPowers := A.gamma
  compatible := A.thickening_compatible

end CrystallineObject

namespace Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime]

/-- The divided-power scheme underlying a prime-local crystalline base. -/
def Base.dividedPowerScheme (B : Base.{u} p) : DividedPowerScheme.{u} :=
  DividedPowerScheme.of B.scheme B.ideal B.quasiCoherent B.dividedPowers B.compatible

/-- The structure map of a relative crystalline thickening preserves the base
ideal and its divided powers. -/
def Evaluation.targetToBase (B : Base.{u} p)
    (A : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed) :
    DividedPowerScheme.Hom A.obj.1.dividedPowerScheme B.dividedPowerScheme where
  base := A.obj.1.thickeningToBase
  ideal_compatible := sorry
  dividedPowers_compatible := A.obj.2

end Scheme.Crystalline
end AlgebraicGeometry
