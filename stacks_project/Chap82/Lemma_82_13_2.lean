/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.EtalePrincipal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom TopologicalSpace

universe u

/- Lemma 82.13.2. For an étale morphism of good algebraic spaces with integral
 target, pullback of a principal divisor is the locally finite unweighted sum
 of the principal divisors on the reduced irreducible components of the source,
 pushed forward along their closed immersions. -/
@[stacks 0EQ2] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.etalePullback_principalDivisor :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
      [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
      (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
      (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ Y) [Etale f] (hf : f ≫ pY = pX)
      [IsIntegral Y] (g : (RationalFunction Y)ˣ),
      let n := deltaDimension pY δ (univIrreducibleClosed Y)
      flatPullback pY pX δ f 0 hf (n - 1)
          (@principalCycle S Y (LocallyOfFiniteType.isLocallyNoetherian pY)
            inferInstance g) =
        AlgebraicCycle.locallyFiniteSum
          (fun η : genericPoints X ↦
            @etaleComponentDivisorPushforward S X Y
              (LocallyOfFiniteType.isLocallyNoetherian pX)
              (IsQuasiSeparated.of_quasiSeparated pX) f inferInstance inferInstance g η)
          (@locallyFinite_etaleComponentDivisorPushforward S X Y
            (LocallyOfFiniteType.isLocallyNoetherian pX)
            (IsQuasiSeparated.of_quasiSeparated pX) f inferInstance inferInstance g))
