/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Degree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward

/-! # Proper pushforward of integral fundamental cycles -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable [UniversallyCatenary B] [IsQuasiSeparated B]
variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- A proper dominant morphism of equal-dimensional integral spaces pushes the
fundamental cycle to its function-field degree times the target fundamental cycle. -/
theorem properPushforward_integralSingleton {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f] (hf : f ≫ pY = pX)
    (n : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = n)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n) :
    properPushforwardCycle pX pY δ f hf
        (integralFundamentalCycle pX) =
      (inducedFunctionFieldDegree f : ℤ) •
        integralFundamentalCycle pY :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
