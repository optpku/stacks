/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.MeromorphicSection
import StacksCheckRecall

/-!
# Gysin of a meromorphic divisor versus first Chern class on a Cartier divisor

On a good integral algebraic space, Gysin pullback of `div_N(t)` along an
effective Cartier divisor equals first-Chern cap of `N` restricted to the
zero scheme of the canonical section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.23.1: Gysin pullback of a meromorphic divisor equals first-Chern
cap with the fundamental cycle of the effective Cartier divisor. -/
@[stacks 0ER9] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.gysin_meromorphicSectionDivisorCycle_eq_firstChernClassCap :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] [IsIntegral X]
      (k : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = (k + 1) + 1)
      (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
      (N : X.Modules) [isInvertibleObject N]
      (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t),
    gysin f δ k D.associatedSheaf D.canonicalSection
        ⟨meromorphicSectionDivisorCycle f δ t ht,
          by simpa only [hX, add_sub_cancel_right] using
            meromorphicSectionDivisorCycle_mem f δ t ht⟩ =
      firstChernClassCap
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ f) δ
          ((Modules.pullback
              (zeroSchemeι D.associatedSheaf D.canonicalSection)).obj N) k
        (closedSubspaceCycleInDegree
          (zeroSchemeι D.associatedSheaf D.canonicalSection ≫ f) δ
          (ClosedSubspace.id (zeroScheme D.associatedSheaf D.canonicalSection).X)
          (k + 1)))
