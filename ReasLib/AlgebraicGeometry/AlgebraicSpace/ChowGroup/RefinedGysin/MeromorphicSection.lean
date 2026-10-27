/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.AssociatedCycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle

/-!
# Refined Gysin pullback of meromorphic divisor cycles

On a good integral algebraic space, refined Gysin pullback of the divisor of a
nonzero meromorphic section along an effective Cartier divisor equals the first
Chern class of the restricted invertible module capped with the divisor's
fundamental cycle. The construction uses the cycle, divisor, and Chow theories
of algebraic spaces; extending it to ringed sites requires those foundations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- On a good integral algebraic space of relative dimension `(k + 1) + 1`,
refined Gysin pullback of the divisor cycle of a nonzero meromorphic section
along an effective Cartier divisor equals the first Chern class of the
restricted invertible module capped with the divisor's degree-`k + 1`
fundamental cycle, in the degree-`k` Chow group of its canonical zero scheme. -/
theorem gysin_meromorphicSectionDivisorCycle_eq_firstChernClassCap
    (k : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = (k + 1) + 1)
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
    (N : X.Modules) [isInvertibleObject N]
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t) :
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
          (k + 1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
