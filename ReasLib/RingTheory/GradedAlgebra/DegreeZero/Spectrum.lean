module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The spectrum of the degree-zero component

@stack 00JO

This leaf relates homogeneous prime ideals to the prime spectrum of the
degree-zero component when a positive-degree homogeneous unit is available.
-/

universe u

namespace PrimeSpectrum

/-- Lemma 10.57.2 (00JO): contraction to degree zero is a homeomorphism from
homogeneous prime ideals when the graded ring has a positive-degree
homogeneous unit. -/
@[stacks 00JO]
theorem isHomeomorph_comap_degreeZero
    {S : Type u} [CommRing S]
    (Agrade : ℤ → Submodule ℤ S) [GradedRing Agrade]
    (hunit : ∃ d > 0, ∃ f : Agrade d, IsUnit (f : S)) :
    IsHomeomorph
      ((comap (algebraMap (Agrade 0) S)) ∘
        (Subtype.val :
          {p : PrimeSpectrum S // p.asIdeal.IsHomogeneous Agrade} →
            PrimeSpectrum S)) := sorry

end PrimeSpectrum
