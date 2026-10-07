module

public import stacks_project.Chap60.Lemma_60_17_2_Object
public import stacks_project.Chap60.Lemma_60_17_2_Coproduct
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits DividedPowers DividedPowers.PAdic CompletedCris

/-- Lemma 60.17.2 (1): in the setup of (60.17.0.1), the completed envelope
`(D, J-bar, γ-bar)` is an object of `Cris^∧(C/A)` in the sense of Remark 60.5.4. -/
@[stacks 07L4]
theorem crystallineD_isCrisWedgeObject
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    (crystallineDCrisObject p I γ π hπ J hJ hIC hpnil hIJ E N hN γhat hγhat).B =
      envelopeCompletionRing p A (MvPolynomial ι A) I γ J hIJ E N hN γhat := sorry

/-- Lemma 60.17.2 (2): in the setup of (60.17.0.4), the completed envelope
`(D(n), J-bar(n), γ-bar(n))` is an object of `Cris^∧(C/A)` in the sense of Remark 60.5.4. -/
@[stacks 07L4]
theorem crystallineDn_isCrisWedgeObject
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) (n : ℕ)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (J : Ideal (tensorPowerCarrier A ι n))
    (hJ : J = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJ : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (tensorPowerCarrier A ι n)) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    (crystallineDnCrisObject p I γ π hπ n hIC hpnil J hJ hIJ E N hN γhat hγhat).B =
      envelopeCompletionRing p A (tensorPowerCarrier A ι n) I γ J hIJ E N hN γhat := sorry

/-- Lemma 60.17.2 (3): `D(n)` is the coproduct of `n + 1` copies of `D` in `Cris^∧(C/A)`. -/
@[stacks 07L4]
theorem crystallineDn_isCoproduct
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
    {n : ℕ} (Jn : Ideal (tensorPowerCarrier A ι n))
    (hJn : Jn = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (tensorPowerCarrier A ι n)) hIJn En)
    (Nn : ℕ) (hNn : Ideal.span {(p : En.D)} ^ Nn ≤ En.D.ideal)
    (γn : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : En.D)}) En.D.ideal Nn hNn)))
    (hγn : DividedPowers.IsDPMorphism En.D.dividedPowers γn
      (algebraMap En.D (AdicCompletion (Ideal.span {(p : En.D)}) En.D))) :
    Nonempty
      (IsColimit
        (crystallineDnCofan p I γ π hπ J hJ hIC hpnil hIJ E hE ND hND γD hγD
          Jn hJn hIJn En Nn hNn γn hγn)) := sorry
