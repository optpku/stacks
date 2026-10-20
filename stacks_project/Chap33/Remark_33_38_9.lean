/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective.IdealMultiple
public import ReasLib.RingTheory.Ideal.Quotient.ReducedCover
import StacksCheckRecall

@[expose] public section

universe u v

/- Remark 33.38.9: If the zero loci of two ideals cover the prime spectrum of a reduced
commutative ring, then the canonical map from the first ideal to its image in the quotient by
the second ideal is bijective. -/
@[stacks 09NW] #check
  (Algebra.idealMap_bijective_of_zeroLocus_union_eq_univ :
    ∀ {A : Type u} [CommRing A] [IsReduced A] (I J : Ideal A),
      PrimeSpectrum.zeroLocus (I : Set A) ∪ PrimeSpectrum.zeroLocus (J : Set A) = Set.univ →
        Function.Bijective (Algebra.idealMap (A ⧸ J) I))

#check
  (Submodule.smulTopQuotientMap_bijective_of_zeroLocus_union_eq_univ :
    ∀ {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]
      [IsReduced A] [Module.Projective A P] (I J : Ideal A),
      PrimeSpectrum.zeroLocus (I : Set A) ∪ PrimeSpectrum.zeroLocus (J : Set A) = Set.univ →
        Function.Bijective (Submodule.smulTopQuotientMap (P := P) I J))
