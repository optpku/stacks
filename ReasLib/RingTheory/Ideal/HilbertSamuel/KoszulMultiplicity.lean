/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Regularity
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Multiplicity

@[expose] public section

open scoped BigOperators

universe u

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The homology modules of the coefficient Koszul complex on generators of an ideal of
definition have finite length. -/
theorem koszulHomology_isFiniteLength (r : ℕ) (I : Ideal R) (f : Fin r → R)
    (hgen : Ideal.span (Set.range f) = I) (hI : I.IsIdealOfDefinition) (i : ℕ) :
    IsFiniteLength R ((RingTheory.Sequence.koszulComplexOnTensorLeft R M f).homology i) := sorry

/-- The degree-`r` Hilbert--Samuel multiplicity is the alternating sum of the lengths of the
homology modules of the coefficient Koszul complex on `r` generators. -/
theorem multiplicityInDegree_eq_koszulHomologyLengthSum (r : ℕ) (I : Ideal R)
    (f : Fin r → R) (hgen : Ideal.span (Set.range f) = I) (hI : I.IsIdealOfDefinition) :
    multiplicityInDegree I M r =
      ((∑ i ∈ Finset.range (r + 1), (Int.negOnePow i : ℤ) *
        ((Module.length R
          ((RingTheory.Sequence.koszulComplexOnTensorLeft R M f).homology i)).toNat : ℤ) : ℤ) : ℚ) := sorry

end Ideal.HilbertSamuel
