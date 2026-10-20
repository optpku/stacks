module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Picard.Depth
public import ReasLib.RingTheory.Depth.RegularQuotient
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open scoped ENat

universe u

/- Remark 52.26.3: for a Noetherian local ring which is a quotient of a regular
ring, a regular element in the maximal ideal, the stated prime-local depth
condition, and quotient depth at least three, restriction from the punctured
spectrum to the punctured closed fiber is injective on Picard groups. -/
@[stacks 0FIX] #check
  (AlgebraicGeometry.PuncturedSpectrum.picardPullback_injective_of_regular_quotient_depth :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
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
      (3 : ℕ∞) ≤ moduleDepth A (A ⧸ Ideal.span ({f} : Set A))),
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := PuncturedSpectrum.puncturedOpen A
    Function.Injective (Scheme.Hom.picardPullback (quotientMap ∣_ punctured)))

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) (hf_regular : IsRegular f)

/- The quotient-depth bound is equivalent to depth at least four for the original
local ring under the same regular-element hypotheses. -/
#check (moduleDepth_quotient_span_singleton_ge_iff f hf_mem hf_regular 3 :
  ((3 : ℕ∞) ≤ moduleDepth A (A ⧸ Ideal.span {f})) ↔
    ((4 : ℕ∞) ≤ moduleDepth A A))

end
