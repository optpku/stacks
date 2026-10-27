/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward.Fundamental
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward.MeromorphicSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward

/-! # First Chern intersection on integral fundamental cycles -/

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

/-- First Chern intersection with the integral fundamental cycle is the Chow
class of the divisor of any regular meromorphic section. -/
theorem firstChernClassCap_integralFundamentalCycle
    (k : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = k + 1)
    (L : X.Modules) [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    firstChernClassCap pX δ L k
        ⟨integralFundamentalCycle pX, integralSingleton_mem_cycleGroup pX δ (k + 1) hX⟩ =
      chowMk pX δ k ⟨meromorphicSectionDivisorCycle pX δ s hs,
        by simpa only [hX, add_sub_cancel_right] using
          meromorphicSectionDivisorCycle_mem pX δ s hs⟩ :=
  sorry

/-- Proper pushforward commutes with first Chern intersection on the fundamental
cycle of a good integral source under a dominant equal-dimensional morphism. -/
theorem properPushforward_firstChernCap_fundamental {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f] (hf : f ≫ pY = pX)
    (k : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = k + 1)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = k + 1)
    (L : Y.Modules) [isInvertibleObject L] :
    ChowGroup.properPushforward pX pY δ f hf k
        (firstChernClassCap pX δ ((Modules.pullback f).obj L) k
          ⟨integralFundamentalCycle pX, integralSingleton_mem_cycleGroup pX δ (k + 1) hX⟩) =
      firstChernClassCap pY δ L k
        (properPushforwardHom pX pY δ f hf (k + 1)
          ⟨integralFundamentalCycle pX, integralSingleton_mem_cycleGroup pX δ (k + 1) hX⟩) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
