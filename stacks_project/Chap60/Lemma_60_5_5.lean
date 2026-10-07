module

import StacksCheckRecall
public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
public import stacks_project.Chap60.Lemma_60_5_5_Stages
public import stacks_project.Chap60.Lemma_60_5_5_Completion

@[expose] public section

universe u

namespace DividedPowers.PAdic

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A P : Type u) [CommRing A] [CommRing P]
variable (I : Ideal A) (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [Algebra A P]
variable (C : Type u) [CommRing C]
variable (f : A →+* C) (π : P →+* C)
variable (hπ_A : π.comp (algebraMap A P) = f)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (J : Ideal P) (hJ : J = RingHom.ker π)
variable (hIJ : Ideal.map (algebraMap A P) I ≤ J)

/- Lemma 60.5.5 (1) -/
@[stacks 07KG]
#check (DividedPowers.PAdic.pAdicEventualDividedPowerStability p A P I γ C f π hπ_A hIC J hJ :
  Function.Surjective π →
    IsNilpotent (p : C) →
      ∀ (E : DividedPowerEnvelope I γ (algebraMap A P) J
        (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ)),
        DividedPowerEnvelope.IsUniversal γ (algebraMap A P)
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E →
          ∃ N : ℕ, 1 ≤ N ∧
            ∃ (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal),
              let γhat := envelopeCompletionDividedPowers E N hN
              let Dhat := envelopeCompletionRing p A P I γ J
                (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E N hN γhat
              ∀ e : ℕ, N ≤ e →
                (Ideal.span {(p : E.D)} ^ e ≤ E.D.ideal ∧
                  DividedPowers.IsSubDPIdeal E.D.dividedPowers
                    (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) ∧
                (Ideal.span {(p : Dhat)} ^ e ≤ Dhat.ideal ∧
                  DividedPowers.IsSubDPIdeal Dhat.dividedPowers
                    (Ideal.span {(p : Dhat)} ^ e ⊓ Dhat.ideal)))

/- Lemma 60.5.5 (2) -/
@[stacks 07KG]
#check (DividedPowers.PAdic.pAdicStageQuotientComparison p A P I γ C f π hπ_A hIC J hJ :
  Function.Surjective π →
    IsNilpotent (p : C) →
      ∀ (E : DividedPowerEnvelope I γ (algebraMap A P) J
        (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ)),
        (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P)
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E) →
          ∀ (EStage : ∀ e : ℕ,
            envelopeStage p A P I γ J
              (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e),
          (∀ e : ℕ,
            DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
              (stageIdeal_contains_base p A P I J
                (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e) (EStage e)) →
          ∃ N : ℕ, 1 ≤ N ∧
            ∃ (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal),
              let γhat := envelopeCompletionDividedPowers E N hN
              let Dhat := envelopeCompletionRing p A P I γ J
                (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E N hN γhat
              ∀ e : ℕ, N ≤ e →
                ∃ (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
                    (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
                  (hstableHat : DividedPowers.IsSubDPIdeal Dhat.dividedPowers
                    (Ideal.span {(p : Dhat)} ^ e ⊓ Dhat.ideal)),
                  CategoryTheory.IsIso
                      (completionQuotientToEnvelopeQuotient p A P I γ J
                        (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E N hN γhat
                        (envelopeCompletionDividedPowers_isDPMorphism E N hN) e
                        hstableHat hstable) ∧
                    CategoryTheory.IsIso
                      (envelopeQuotientToStage p A P I γ J
                        (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E
                        hE e hstable (EStage e)))

/- Lemma 60.5.5 (3) -/
@[stacks 07KG]
#check (DividedPowers.PAdic.envelopeStageIsCrisObject p A P I γ C f π hπ_A hIC J hJ :
  (hπ : Function.Surjective π) →
    (h_pC : IsNilpotent (p : C)) →
      ∀ (EStage : ∀ e : ℕ,
        envelopeStage p A P I γ J
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e),
      (hEStage : ∀ e : ℕ,
        DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
          (stageIdeal_contains_base p A P I J
            (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e) (EStage e)) →
      ∃ N : ℕ, 1 ≤ N ∧
        ∀ e : ℕ, N ≤ e →
          ∃ h_pCe : (p : C) ^ e = 0,
            DividedPowerThickening.isCrisObject γ f hIC h_pC
              (envelopeStageThickening p γ f π hπ hπ_A hIC h_pC hJ e (EStage e)) ∧
              (envelopeStageCrisObject p γ f π hπ hπ_A hIC h_pC hJ e (EStage e)
                (hEStage e) h_pCe).obj.B = (EStage e).D)

/- Lemma 60.5.5 (4) -/
@[stacks 07KG]
#check (DividedPowers.PAdic.pAdicCompletionIsInverseLimit p A P I γ C f π hπ_A hIC J hJ :
  (hπ : Function.Surjective π) →
    (h_pC : IsNilpotent (p : C)) →
      ∀ (E : DividedPowerEnvelope I γ (algebraMap A P) J
        (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ)),
        (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P)
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E) →
        ∀ (EStage : ∀ e : ℕ,
          envelopeStage p A P I γ J
            (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e),
        (hEStage : ∀ e : ℕ,
          DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
            (stageIdeal_contains_base p A P I J
              (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e) (EStage e)) →
        ∀ (N : ℕ),
          (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal) →
          (hstable : IsStableUnderPowers E.D.dividedPowers (Ideal.span {(p : E.D)}) N) →
          let γhat := envelopeCompletionDividedPowers E N hN
          let Dhat := envelopeCompletionRing p A P I γ J
            (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E N hN γhat
          let completionCone := envelopeStageCompletionCone p A P I γ J
            (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) EStage hEStage E hE N hN hstable γhat
            (envelopeCompletionDividedPowers_isDPMorphism E N hN)
          completionCone.pt = Dhat ∧ Nonempty (CategoryTheory.Limits.IsLimit completionCone))

/- Lemma 60.5.5 (5) -/
@[stacks 07KG]
#check (DividedPowers.PAdic.pAdicCompletionIsCrisWedgeObject p A P I γ C f π hπ_A hIC J hJ :
  (hπ : Function.Surjective π) →
    (h_pC : IsNilpotent (p : C)) →
      ∀ (E : DividedPowerEnvelope I γ (algebraMap A P) J
        (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ)),
        (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P)
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E) →
          ∃ N : ℕ, 1 ≤ N ∧
            ∃ (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal),
              let γhat := envelopeCompletionDividedPowers E N hN
              let Dhat := envelopeCompletionRing p A P I γ J
                (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E N hN γhat
              (envelopeCompletedCrisObject p γ f π
                hπ hπ_A hIC h_pC hJ E hE N hN γhat
                (envelopeCompletionDividedPowers_isDPMorphism E N hN) :
                CompletedCrisObject p A I γ C f hIC h_pC).B = Dhat)

end DividedPowers.PAdic
