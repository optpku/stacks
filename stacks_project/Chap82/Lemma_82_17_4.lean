/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor.DivisorCycle
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 82.17.4. In Situation 82.2.1, for good integral `X / B`, an invertible
module `L`, and a nonzero meromorphic section `s`, pullback of `div_L(s)` along
its canonical multiplicative torsor is the divisor of the pulled-back section
viewed as a meromorphic function through the tautological trivialization.
Regularity expresses nonvanishing for an invertible module on integral `X`. -/
@[stacks 0EQH] #check
  (AlgebraicGeometry.AlgebraicSpace.gmTorsorπ_meromorphicSectionDivisorCycle :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L)
      (hs : IsRegularMeromorphicSection X L s),
      Hom.flatPullback f (Modules.gmTorsorπ L ≫ f) δ (Modules.gmTorsorπ L) 1 rfl
          (Hom.deltaDimension f δ (univIrreducibleClosed X) - 1)
          (Hom.meromorphicSectionDivisorCycle f δ s hs) =
        Hom.meromorphicSectionDivisorCycle (Modules.gmTorsorπ L ≫ f) δ
          (gmTorsorTrivMeromorphicSection L s)
          (isRegularMeromorphicSection_gmTorsorTriv L s hs))
