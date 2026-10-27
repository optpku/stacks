/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Degree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.RegularPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward

/-! # Proper pushforward of meromorphic-section divisors -/

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

/-- Pushing forward the divisor of a pulled-back regular meromorphic section
along a proper dominant equal-dimensional integral morphism multiplies its
divisor by the induced function-field degree. -/
theorem properPushforward_meromorphicSectionDivisor {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f] (hf : f ≫ pY = pX)
    (n : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = n)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    properPushforwardHom pX pY δ f hf (n - 1)
        ⟨meromorphicSectionDivisorCycle pX δ (MeromorphicConstruction.Pullback.pullback f L s)
          (isRegularMeromorphicSection_pullback f L hs),
          by
            simpa only [hX] using
              meromorphicSectionDivisorCycle_mem pX δ
                (MeromorphicConstruction.Pullback.pullback f L s)
                (isRegularMeromorphicSection_pullback f L hs)⟩ =
      (inducedFunctionFieldDegree f : ℤ) •
        ⟨meromorphicSectionDivisorCycle pY δ s hs,
          by simpa only [hY] using meromorphicSectionDivisorCycle_mem pY δ s hs⟩ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
