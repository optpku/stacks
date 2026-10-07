module

public import ReasLib.RingTheory.AdicCompletion.LocalizationAway.Ideal
import StacksCheckRecall

/-!
# Prime ideals after completed principal localization

If `A` is an adic Noetherian topological ring, `p` is prime, and `f` maps to a
unit in `A ⧸ p`, then the extended ideal of `p` in the completed principal
localization `completedPrincipalLocalization I f` is prime, and it is identified
with `p ⊗[A] completedPrincipalLocalization I f` and with the completion of
`LocalizedModule.Away f p`. The quotient `A ⧸ p` is identified with the
corresponding quotient of the completed localization and with
`(A ⧸ p) ⊗[A] completedPrincipalLocalization I f`.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace completedPrincipalLocalization

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/- Lemma 88.14.8: a prime ideal remains prime after completed principal
localization at an element that is a unit modulo the ideal, with the tensor,
localized-completion, quotient, and quotient-tensor identifications below. -/
@[stacks 0GGF] #check (completedPrincipalLocalization.map_isPrime :
  ∀ (I : Ideal A) [Fact (IsAdic I)] (p : Ideal A) [p.IsPrime]
    (f : A) [Fact (IsUnit (Ideal.Quotient.mk p f))],
    (p.map (algebraMap A (completedPrincipalLocalization I f))).IsPrime)

#check (completedPrincipalLocalization.map_ofTensor_linearEquiv :
  ∀ (I : Ideal A), IsAdic I → ∀ (p : Ideal A) [p.IsPrime] (f : A),
    IsUnit (Ideal.Quotient.mk p f) →
    p ⊗[A] completedPrincipalLocalization I f ≃ₗ[A]
      (p.map (algebraMap A (completedPrincipalLocalization I f))).restrictScalars A)

#check (completedPrincipalLocalization.map_ofTensor_linearEquiv_apply :
  ∀ (I : Ideal A) (hI : IsAdic I) (p : Ideal A) [p.IsPrime]
    (f : A) (hf : IsUnit (Ideal.Quotient.mk p f))
    (x : A) (hx : x ∈ p) (b : completedPrincipalLocalization I f),
    (map_ofTensor_linearEquiv I hI p f hf (⟨x, hx⟩ ⊗ₜ b)).1 = x • b)

#check (completedPrincipalLocalization.localizedCompletion_linearEquiv :
  ∀ (I : Ideal A), IsAdic I → ∀ (p : Ideal A) [p.IsPrime] (f : A),
    IsUnit (Ideal.Quotient.mk p f) →
    AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (LocalizedModule.Away f p) ≃ₗ[completedPrincipalLocalization I f]
      p.map (algebraMap A (completedPrincipalLocalization I f)))

#check (completedPrincipalLocalization.localizedCompletion_linearEquiv_apply :
  ∀ (I : Ideal A) (hI : IsAdic I) (p : Ideal A) [p.IsPrime]
    (f : A) (hf : IsUnit (Ideal.Quotient.mk p f))
    (x : AdicCompletion (I.map (algebraMap A (Localization.Away f)))
      (LocalizedModule.Away f p)),
    (localizedCompletion_linearEquiv I hI p f hf x).1 =
      AdicCompletion.map (I.map (algebraMap A (Localization.Away f)))
        (LocalizedModule.map (Submonoid.powers f) p.subtype) x)

#check (completedPrincipalLocalization.quotient_algEquiv :
  ∀ (I : Ideal A), IsAdic I → ∀ (p : Ideal A) [p.IsPrime] (f : A),
    IsUnit (Ideal.Quotient.mk p f) →
    (A ⧸ p) ≃ₐ[A] completedPrincipalLocalization I f ⧸
      p.map (algebraMap A (completedPrincipalLocalization I f)))

#check (completedPrincipalLocalization.quotient_algEquiv_apply :
  ∀ (I : Ideal A) (hI : IsAdic I) (p : Ideal A) [p.IsPrime]
    (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) (a : A),
    quotient_algEquiv I hI p f hf (Ideal.Quotient.mk p a) =
      Ideal.Quotient.mk (p.map (algebraMap A (completedPrincipalLocalization I f)))
        (algebraMap A (completedPrincipalLocalization I f) a))

#check (completedPrincipalLocalization.quotient_tensor_algEquiv :
  ∀ (I : Ideal A), IsAdic I → ∀ (p : Ideal A) [p.IsPrime] (f : A),
    IsUnit (Ideal.Quotient.mk p f) →
    (A ⧸ p) ≃ₐ[A] (A ⧸ p) ⊗[A] completedPrincipalLocalization I f)

#check (completedPrincipalLocalization.quotient_tensor_algEquiv_apply :
  ∀ (I : Ideal A) (hI : IsAdic I) (p : Ideal A) [p.IsPrime]
    (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) (x : A ⧸ p),
    quotient_tensor_algEquiv I hI p f hf x = x ⊗ₜ (1 : completedPrincipalLocalization I f))

end completedPrincipalLocalization
