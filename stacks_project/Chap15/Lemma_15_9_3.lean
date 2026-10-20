module

public import ReasLib.RingTheory.Etale.DisjointCover
import StacksCheckRecall

/-!
# Lemma 15.9.3

@stack 07LZ
-/

@[expose] public section

open PrimeSpectrum Set TopologicalSpace

universe u v

namespace Algebra

variable {A : Type u} [CommRing A]
variable {ι : Type v} [Finite ι]

-- Lemma 15.9.3 (07LZ): etale-local lifting of a finite disjoint spectral open cover.
@[stacks 07LZ]
#check
  (exists_etale_lift_of_finite_disjoint_open_cover_of_spec_quotient :
    (I : Ideal A) → (Ubar : ι → Opens (PrimeSpectrum (A ⧸ I))) →
      IsOpenCover Ubar →
      (Pairwise fun i j ↦
        Disjoint (Ubar i : Set (PrimeSpectrum (A ⧸ I)))
          (Ubar j : Set (PrimeSpectrum (A ⧸ I)))) →
      ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
        (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ I.map (algebraMap A A')))
        (U' : ι → Opens (PrimeSpectrum A')),
          IsOpenCover U' ∧
            (Pairwise fun i j ↦
              Disjoint (U' i : Set (PrimeSpectrum A')) (U' j : Set (PrimeSpectrum A'))) ∧
            ∀ j,
              comap eIso.toRingHom ⁻¹' (Ubar j : Set (PrimeSpectrum (A ⧸ I))) =
                comap (Ideal.Quotient.mk (I.map (algebraMap A A'))) ⁻¹'
                  (U' j : Set (PrimeSpectrum A')))

end Algebra
