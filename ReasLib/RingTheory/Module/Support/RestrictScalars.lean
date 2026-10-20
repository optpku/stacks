module

public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Support under a surjective scalar map

The support of a module with a surjective scalar action is obtained by
contracting prime ideals along the scalar map.  This is the neutral owner for
quotient-ring support arguments.
-/

@[expose] public section

universe u v w

open PrimeSpectrum

namespace Module

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

/-- Membership in support is preserved by restricting scalars along a
surjective algebra map. -/
theorem mem_support_restrictScalars_iff_of_surjective
    (hmap : Function.Surjective (algebraMap R S))
    (q : PrimeSpectrum S) :
    q ∈ support S M ↔
      PrimeSpectrum.comap (algebraMap R S) q ∈ support R M := sorry

/-- A surjective scalar map identifies support over the target with the
preimage of support over the source. -/
theorem support_eq_preimage_comap_of_surjective
    (hmap : Function.Surjective (algebraMap R S)) :
    support S M = PrimeSpectrum.comap (algebraMap R S) ⁻¹' support R M := sorry

/-- Full support descends along a surjective scalar map. -/
theorem support_eq_univ_of_surjective
    (hmap : Function.Surjective (algebraMap R S))
    (hsupp : support R M = Set.univ) :
    support S M = Set.univ := sorry

end Module
