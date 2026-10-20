module

public import stacks_project.Chap52.«52_25_1_1_EulerCharacteristic»
public import ReasLib.RingTheory.Depth.RegularQuotient
public import ReasLib.RingTheory.Depth.Dualizing
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Picard.Depth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open scoped ENat

universe u

/- Proposition 52.26.2 (Kollár): Picard pullback from the punctured spectrum
to its regular principal closed fiber is injective under the dualizing and
depth hypotheses. -/
@[stacks 0F2B] #check
  (AlgebraicGeometry.PuncturedSpectrum.picardPullback_injective_of_dualizing_depth :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)
    (h_depth : (3 : ℕ∞) ≤ moduleDepth A A)
    (h_prime_depth : ∀ p : PrimeSpectrum A,
      f ∈ p.asIdeal →
        ringKrullDim (A ⧸ p.asIdeal) = (2 : WithBot ℕ∞) →
          (2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal)),
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := PuncturedSpectrum.puncturedOpen A
    Function.Injective (Scheme.Hom.picardPullback (quotientMap ∣_ punctured)))

/- The final assertion derives the primewise depth condition from `(S₂)` and
dimension at least four. -/
#check (SerreConditionS.primeDepth_ge_two_of_dualizing_dimension :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)
    (h_depth : (3 : ℕ∞) ≤ moduleDepth A A)
    [SerreConditionS A 2]
    (h_dim : (4 : WithBot ℕ∞) ≤ ringKrullDim A),
    ∀ p : PrimeSpectrum A,
      f ∈ p.asIdeal →
        ringKrullDim (A ⧸ p.asIdeal) = (2 : WithBot ℕ∞) →
          (2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal))

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) (hf_regular : IsRegular f)

/- The equivalent quotient-depth formulation of the depth-three hypothesis. -/
#check (moduleDepth_quotient_span_singleton_ge_iff f hf_mem hf_regular 2 :
  ((2 : ℕ∞) ≤ moduleDepth A (A ⧸ Ideal.span {f})) ↔
    ((3 : ℕ∞) ≤ moduleDepth A A))

end
