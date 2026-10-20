module

public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
import StacksCheckRecall

open DividedPowers DividedPowers.PAdic

@[expose] public section

universe u

/- Lemma 60.5.6: in Situation 60.5.1, if `P` is a polynomial `A`-algebra and
`π : P → C` is a surjection of `A`-algebras with kernel `J`, then for the
finite envelope stages `(D_e, J̄_e, γ̄)` of Lemma 60.5.5, every object of
`CRIS(C/A)` receives a morphism from some `D_e`. -/
@[stacks 07HP] #check (DividedPowers.PAdic.existsEnvelopeStageHom :
    ∀ (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A]
    (I : Ideal A) (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (C : Type u) [CommRing C] [Algebra A C]
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C))
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π)
    (hπ_A : π.toRingHom.comp (algebraMap A (MvPolynomial ι A)) = algebraMap A C)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (EStage : ∀ e : ℕ,
      envelopeStage p A (MvPolynomial ι A) I γ J
        (pAdicBaseIdealLeKernel I (algebraMap A C) π.toRingHom J hπ_A hIC hJ) e)
    (hEStage : ∀ e : ℕ,
      DividedPowerEnvelope.IsUniversal γ (stageMap p A (MvPolynomial ι A) e)
        (stageIdeal_contains_base p A (MvPolynomial ι A) I J
          (pAdicBaseIdealLeKernel I (algebraMap A C) π.toRingHom J hπ_A hIC hJ) e)
        (EStage e))
    (B : DividedPowerThickening.CRIS γ (algebraMap A C) hIC h_pC),
    ∃ e : ℕ, Nonempty
      (DividedPowerThickening.Hom γ (algebraMap A C)
        (envelopeStageThickening p γ (algebraMap A C) π.toRingHom
          hπ hπ_A hIC h_pC hJ e (EStage e)) B))
