/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.KrullDimension
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.MaximalIdeal

@[expose] public section

universe u

namespace Ideal.LocalCohomology

/-- If the zero loci of a prime ideal and a proper ideal of a Noetherian local ring
intersect only at the closed point, then the Krull dimension of the quotient by the
prime is at most the local-cohomological dimension of the proper ideal. -/
theorem dimension_quotient_le_of_zeroLocus_inter_eq_closedPoint {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤)
    (p : PrimeSpectrum A)
    (hV : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) = {IsLocalRing.closedPoint A}) :
    WithBot.map (WithTop.map Int.ofNat) (ringKrullDim (A ⧸ p.asIdeal)) ≤
      (dimension I I.fg_of_isNoetherianRing : EInt) := sorry

end Ideal.LocalCohomology
