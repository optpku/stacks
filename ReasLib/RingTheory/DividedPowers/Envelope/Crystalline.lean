/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Tower
public import ReasLib.RingTheory.DividedPowers.CrystallineCompletion
public import ReasLib.RingTheory.DividedPowers.Thickening.Category
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits DividedPowers Opposite

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
/-- The finite envelope stage defines a divided-power thickening of the target. -/
noncomputable def envelopeStageThickening
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (f : A →+* C) (π : P →+* C) (hπ : Function.Surjective π)
    (hπ_A : π.comp (algebraMap A P) = f)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C))
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e) :
    DividedPowerThickening p A I γ C f hIC h_pC :=
  DividedPowerThickening.of γ f hIC h_pC
    EStage.D EStage.base
    (envelopeStage_p_nilpotent p e EStage)
    (envelopeStageQuotientMap p π hπ hJ e EStage)
    (envelopeStageQuotientMap_comm p f π hπ hπ_A hJ e EStage)

/-- The finite-stage thickening has an invertible quotient map under the universal and nilpotent hypotheses. -/
theorem envelopeStageThickening_isCrisObject
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (f : A →+* C) (π : P →+* C) (hπ : Function.Surjective π)
    (hπ_A : π.comp (algebraMap A P) = f)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C))
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e)
    (hEStage : DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
      (stageIdeal_contains_base p A P I J hIJ e) EStage)
    (h_pCe : (p : C) ^ e = 0) :
    DividedPowerThickening.isCrisObject γ f hIC h_pC
      (envelopeStageThickening p γ f π hπ hπ_A hIC h_pC hJ e EStage) := sorry

/-- The `Cris(C/A)` object on a finite envelope stage. -/
noncomputable def envelopeStageCrisObject
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (f : A →+* C) (π : P →+* C) (hπ : Function.Surjective π)
    (hπ_A : π.comp (algebraMap A P) = f)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C))
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e)
    (hEStage : DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
      (stageIdeal_contains_base p A P I J hIJ e) EStage)
    (h_pCe : (p : C) ^ e = 0) :
    DividedPowerThickening.Cris γ f hIC h_pC where
  obj := envelopeStageThickening p γ f π hπ hπ_A hIC h_pC hJ e EStage
  property := envelopeStageThickening_isCrisObject p γ f π hπ hπ_A hIC h_pC hJ e EStage
    hEStage h_pCe

/-- The underlying ring of `envelopeStageCrisObject` is the finite envelope stage. -/
theorem envelopeStageCrisObject_B
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (f : A →+* C) (π : P →+* C) (hπ : Function.Surjective π)
    (hπ_A : π.comp (algebraMap A P) = f)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C))
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e)
    (hEStage : DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
      (stageIdeal_contains_base p A P I J hIJ e) EStage)
    (h_pCe : (p : C) ^ e = 0) :
    (envelopeStageCrisObject p γ f π hπ hπ_A hIC h_pC hJ e EStage hEStage h_pCe).obj.B = EStage.D := sorry

/-- The completed envelope determines a completed crystalline object. -/
noncomputable def envelopeCompletedCrisObject
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (f : A →+* C) (π : P →+* C) (hπ : Function.Surjective π)
    (hπ_A : π.comp (algebraMap A P) = f)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C))
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    CompletedCrisObject p A I γ C f hIC h_pC :=
  CompletedCrisObject.of γ f hIC h_pC
    (envelopeCompletionRing p A P I γ J hIJ E N hN γhat)
    (envelopeCompletionBase p E N hN γhat hγhat)
    (envelopeCompletionToC p π hπ hJ E hE N hN γhat)
    (envelopeCompletionToC_surjective p π hπ hJ E hE N hN γhat)
    (envelopeCompletionToC_ker p π hπ hJ E hE N hN γhat)
    (envelopeCompletionToC_comm p f π hπ hπ_A hJ E hE N hN γhat hγhat)
    (envelopeCompletion_isAdicComplete p E N hN γhat)

/-- The underlying ring of `envelopeCompletedCrisObject` is the named envelope completion. -/
theorem envelopeCompletedCrisObject_B
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (f : A →+* C) (π : P →+* C) (hπ : Function.Surjective π)
    (hπ_A : π.comp (algebraMap A P) = f)
    (hIC : Ideal.map f I = (⊥ : Ideal C))
    (h_pC : IsNilpotent (p : C))
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    (envelopeCompletedCrisObject p γ f π hπ hπ_A hIC h_pC hJ E hE N hN γhat hγhat).B =
      envelopeCompletionRing p A P I γ J hIJ E N hN γhat := sorry
/-- Sufficiently high powers of `p` lie in the distinguished ideals and are divided-power stable. -/
theorem pAdicEventualDividedPowerStability
    (hπ : Function.Surjective π) (h_pC : IsNilpotent (p : C))
    (E : DividedPowerEnvelope I γ (algebraMap A P) J
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ))
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P)
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E) :
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
              (Ideal.span {(p : Dhat)} ^ e ⊓ Dhat.ideal)) := sorry

/-- The completed and finite envelope quotients agree on a sufficiently large tail. -/
theorem pAdicStageQuotientComparison
    (hπ : Function.Surjective π) (h_pC : IsNilpotent (p : C))
    (E : DividedPowerEnvelope I γ (algebraMap A P) J
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ))
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P)
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E)
    (EStage : ∀ e : ℕ,
      envelopeStage p A P I γ J (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e)
    (hEStage : ∀ e : ℕ,
      DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
        (stageIdeal_contains_base p A P I J
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e) (EStage e)) :
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
            IsIso
                (completionQuotientToEnvelopeQuotient p A P I γ J
                  (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E N hN γhat
                  (envelopeCompletionDividedPowers_isDPMorphism E N hN) e
                  hstableHat hstable) ∧
              IsIso
                (envelopeQuotientToStage p A P I γ J
                  (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E hE e hstable
                  (EStage e)) := sorry

/-- Finite envelope stages are crystalline objects on a sufficiently large tail. -/
theorem envelopeStageIsCrisObject
    (hπ : Function.Surjective π) (h_pC : IsNilpotent (p : C))
    (EStage : ∀ e : ℕ,
      envelopeStage p A P I γ J (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e)
    (hEStage : ∀ e : ℕ,
      DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
        (stageIdeal_contains_base p A P I J
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e) (EStage e)) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ e : ℕ, N ≤ e →
        ∃ h_pCe : (p : C) ^ e = 0,
        DividedPowerThickening.isCrisObject γ f hIC h_pC
            (envelopeStageThickening p γ f π hπ hπ_A hIC h_pC hJ e (EStage e)) ∧
          (envelopeStageCrisObject p γ f π hπ hπ_A hIC h_pC hJ e (EStage e) (hEStage e) h_pCe).obj.B =
            (EStage e).D := sorry

/-- The completed divided-power ring is the inverse limit of the finite-envelope tower. -/
theorem pAdicCompletionIsInverseLimit
    (hπ : Function.Surjective π) (h_pC : IsNilpotent (p : C))
    (E : DividedPowerEnvelope I γ (algebraMap A P) J
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ))
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P)
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E)
    (EStage : ∀ e : ℕ,
      envelopeStage p A P I γ J (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e)
    (hEStage : ∀ e : ℕ,
      DividedPowerEnvelope.IsUniversal γ (stageMap p A P e)
        (stageIdeal_contains_base p A P I J
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) e) (EStage e))
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (hstable : IsStableUnderPowers E.D.dividedPowers
      (Ideal.span {(p : E.D)}) N) :
    let γhat := envelopeCompletionDividedPowers E N hN
    let Dhat := envelopeCompletionRing p A P I γ J
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E N hN γhat
    let completionCone := envelopeStageCompletionCone p A P I γ J
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) EStage hEStage
      E hE N hN hstable γhat
      (envelopeCompletionDividedPowers_isDPMorphism E N hN)
    completionCone.pt = Dhat ∧
      Nonempty (IsLimit completionCone) := sorry

/-- The completed envelope is a completed crystalline object with the stated underlying ring. -/
theorem pAdicCompletionIsCrisWedgeObject
    (hπ : Function.Surjective π) (h_pC : IsNilpotent (p : C))
    (E : DividedPowerEnvelope I γ (algebraMap A P) J
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ))
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P)
      (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∃ (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal),
        let γhat := envelopeCompletionDividedPowers E N hN
        let Dhat := envelopeCompletionRing p A P I γ J
          (pAdicBaseIdealLeKernel I f π J hπ_A hIC hJ) E N hN γhat
        (envelopeCompletedCrisObject p γ f π hπ hπ_A hIC h_pC hJ E hE N hN γhat
            (envelopeCompletionDividedPowers_isDPMorphism E N hN) :
              CompletedCrisObject p A I γ C f hIC h_pC).B =
          Dhat := sorry

/-- Every crystalline thickening receives a compatible divided-power morphism from some
universal finite envelope stage of a polynomial presentation of the base algebra. -/
theorem existsEnvelopeStageHom
    (p : ℕ) [Fact (Nat.Prime p)]
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
    (B : DividedPowerThickening.CRIS γ (algebraMap A C) hIC h_pC) :
    ∃ e : ℕ, Nonempty
      (DividedPowerThickening.Hom γ (algebraMap A C)
        (envelopeStageThickening p γ (algebraMap A C) π.toRingHom
          hπ hπ_A hIC h_pC hJ e (EStage e)) B) := sorry

end DividedPowers.PAdic
