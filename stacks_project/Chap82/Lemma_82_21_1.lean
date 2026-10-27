/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle.Commutativity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.21.1: In Situation 82.2.1 let `X / B` be good. Assume `X` integral
and `dim_δ(X) = n`. Let `L`, `N` be invertible on `X`. Choose a nonzero
meromorphic section `s` of `L` and a nonzero meromorphic section `t` of `N`.
Set `α = div_L(s)` and `β = div_N(t)`. Then `c1(N) ∩ α = c1(L) ∩ β` in
`CH_{n-2}(X)`. -/
@[stacks 0EQX]
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap_meromorphicSectionDivisor_comm :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t),
    firstChernClassCap f δ N (n - 2)
        ⟨meromorphicSectionDivisorCycle f δ s hs, by
          simpa only [hX, show n - 1 = (n - 2) + 1 by omega] using
            meromorphicSectionDivisorCycle_mem f δ s hs⟩ =
      firstChernClassCap f δ L (n - 2)
        ⟨meromorphicSectionDivisorCycle f δ t ht, by
          simpa only [hX, show n - 1 = (n - 2) + 1 by omega] using
            meromorphicSectionDivisorCycle_mem f δ t ht⟩)
