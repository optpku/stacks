/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Ideal quotients from a reduced spectral cover

Two ideals whose zero loci cover the prime spectrum of a reduced ring have zero intersection.
Consequently, quotienting by either ideal is injective on the other ideal.
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [CommRing A] [IsReduced A]

/-- If the zero loci of two ideals cover the prime spectrum of a reduced ring, then the ideals
have zero intersection. -/
theorem inf_eq_bot_of_zeroLocus_union_eq_univ (I J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (I : Set A) ∪
      PrimeSpectrum.zeroLocus (J : Set A) = Set.univ) :
    I ⊓ J = ⊥ := sorry

end Ideal

namespace Algebra

variable {A : Type u} [CommRing A]

/-- If two ideals have zero intersection, then the canonical map from the first ideal to its
image in the quotient by the second ideal is bijective. -/
theorem idealMap_bijective_of_inf_eq_bot (I J : Ideal A) (hIJ : I ⊓ J = ⊥) :
    Function.Bijective (Algebra.idealMap (A ⧸ J) I) := sorry

/-- If the zero loci of two ideals cover the prime spectrum of a reduced ring, then the canonical
map from the first ideal to its image in the quotient by the second ideal is bijective. -/
theorem idealMap_bijective_of_zeroLocus_union_eq_univ [IsReduced A] (I J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (I : Set A) ∪
      PrimeSpectrum.zeroLocus (J : Set A) = Set.univ) :
    Function.Bijective (Algebra.idealMap (A ⧸ J) I) := sorry

end Algebra
