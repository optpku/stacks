/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle

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

/-- On an integral algebraic space of dimension `n`, intersecting the divisor of
one regular meromorphic section with the first Chern class of a second invertible
module is symmetric in the two modules and sections, in the Chow group of degree
`n - 2`. -/
theorem firstChernClassCap_meromorphicSectionDivisor_comm
    (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t) :
    firstChernClassCap f δ N (n - 2)
        ⟨meromorphicSectionDivisorCycle f δ s hs, by
          simpa only [hX, show n - 1 = (n - 2) + 1 by omega] using
            meromorphicSectionDivisorCycle_mem f δ s hs⟩ =
      firstChernClassCap f δ L (n - 2)
        ⟨meromorphicSectionDivisorCycle f δ t ht, by
          simpa only [hX, show n - 1 = (n - 2) + 1 by omega] using
            meromorphicSectionDivisorCycle_mem f δ t ht⟩ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
