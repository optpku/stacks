module

public import stacks_project.Chap52.Proposition_52_26_2_Koll_r
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.CoherentTripleSetup

/-- Remark 52.26.3: for a Noetherian local ring which is a quotient of a regular
ring, a regular element in the maximal ideal, the stated prime-local depth
condition, and quotient depth at least three, restriction from the punctured
spectrum to the punctured closed fiber is injective on Picard groups. -/
@[stacks 0FIX]
theorem picardPullback_injective_of_regular_quotient_depth
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (h_quotient_regular :
      ∃ (R : Type u) (_ : CommRing R) (_ : IsRegularRing R)
        (φ : R →+* A), Function.Surjective φ)
    (h_prime_depth : ∀ p : PrimeSpectrum A,
      ringKrullDim (A ⧸ p.asIdeal) = (1 : WithBot ℕ∞) →
        (2 : ℕ∞) ≤
          moduleDepth (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal))
    (h_depth_quotient :
      (3 : ℕ∞) ≤ moduleDepth A (A ⧸ Ideal.span ({f} : Set A))) :
    let S := CoherentTripleSetup.ofElement f hf_mem hf_regular
    Function.Injective (Scheme.Hom.picardPullback S.closedFiberOnU) := sorry

/-- The quotient-depth bound in Remark 52.26.3 is equivalent to depth at least
four for the original local ring under the same regular-element hypotheses. -/
@[stacks 0FIX]
theorem depth_quotient_ge_three_iff_depth_ge_four
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    ((3 : ℕ∞) ≤ moduleDepth A (A ⧸ Ideal.span ({f} : Set A))) ↔
      ((4 : ℕ∞) ≤ moduleDepth A A) := sorry

end AlgebraicGeometry.CoherentTripleSetup
