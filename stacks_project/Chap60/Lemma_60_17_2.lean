/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Coproduct
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits DividedPowers DividedPowers.PAdic

/- Lemma 60.17.2: the completed polynomial and tensor envelopes are objects of
Cris^∧(C/A), and the tensor envelope is the coproduct of n + 1 polynomial envelopes. -/
@[stacks 07L4] #check (DividedPowerEnvelope.TensorPower.isCoproduct : ∀
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (ND : ℕ) (hND : Ideal.span {(p : E.D)} ^ ND ≤ E.D.ideal)
    (γD : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal ND hND)))
    (hγD : DividedPowers.IsDPMorphism E.D.dividedPowers γD
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D))),
    Nonempty
      (IsColimit
        (DividedPowerEnvelope.TensorPower.cofan p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
          Jn hJn hIJn En hEn Nn hNn γn hγn)))

section

variable
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (ND : ℕ) (hND : Ideal.span {(p : E.D)} ^ ND ≤ E.D.ideal)
    (γD : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal ND hND)))
    (hγD : DividedPowers.IsDPMorphism E.D.dividedPowers γD
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    {n : ℕ} (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D)))

#check (DividedPowers.PAdic.envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
    π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD :
  CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil)

#check (DividedPowerEnvelope.TensorPower.completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn :
  CompletedCrisObject p A I γ C (algebraMap A C) hIC hpnil)

#check (DividedPowers.PAdic.envelopeCompletedCrisObject_B p γ (algebraMap A C) π.toRingHom hπ
    π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD :
  (envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ
        π.comp_algebraMap hIC hpnil hJ E hE ND hND γD hγD).B =
    envelopeCompletionRing p A (MvPolynomial ι A) I γ J hIJ E ND hND γD)

#check (DividedPowerEnvelope.TensorPower.completedCrisObject_B p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn :
  (DividedPowerEnvelope.TensorPower.completedCrisObject p I γ π hπ n hIC hpnil Jn hJn hIJn En hEn Nn hNn γn hγn).B =
    envelopeCompletionRing p A (MvPolynomial.TensorPower.carrier A ι n) I γ Jn hIJn En Nn hNn γn)

end
