/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward.MeromorphicSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernFundamental

/-! # Proper pushforward of meromorphic divisors and first Chern intersection -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

/- Lemma 82.19.3: a proper dominant morphism of good integral algebraic spaces
of equal delta dimension pushes the divisor of a pulled-back nonzero meromorphic
section to the function-field degree times its divisor. -/
@[stacks 0EQS] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_meromorphicSectionDivisor :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f] (hf : f ≫ pY = pX)
    (n : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = n)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s),
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
          by simpa only [hY] using meromorphicSectionDivisorCycle_mem pY δ s hs⟩)

/- The first-Chern consequence of Lemma 82.19.3 is independent of a choice of
meromorphic section. The printed source has `f_*[Y]`; its proof explicitly uses
`f_*[X] = [R(X) : R(Y)] [Y]`, giving the well-typed identity below. -/
@[stacks 0EQS] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_firstChernCap_fundamental :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    {Y : AlgebraicSpace S}
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f] (hf : f ≫ pY = pX)
    (k : ℤ) (hX : deltaDimension pX δ (univIrreducibleClosed X) = k + 1)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = k + 1)
    (L : Y.Modules) [isInvertibleObject L],
    ChowGroup.properPushforward pX pY δ f hf k
        (firstChernClassCap pX δ ((Modules.pullback f).obj L) k
          ⟨integralFundamentalCycle pX, integralSingleton_mem_cycleGroup pX δ (k + 1) hX⟩) =
      firstChernClassCap pY δ L k
        (properPushforwardHom pX pY δ f hf (k + 1)
          ⟨integralFundamentalCycle pX, integralSingleton_mem_cycleGroup pX δ (k + 1) hX⟩))
