module

public import stacks_project.Chap60.Lemma_60_5_5
public import stacks_project.Chap60.Lemma_60_5_5_CrisWedge
public import stacks_project.Chap60.«60_17_0_1»
public import stacks_project.Chap60.«60_17_0_4»
public import stacks_project.Chap60.«60_17_0_4_TensorPower»

@[expose] public section

universe u

open DividedPowers DividedPowers.PAdic

/-- The completed envelope of the polynomial presentation as an object of `Cris^∧(C/A)`. -/
noncomputable def crystallineDCrisObject
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    DividedPowerThickening.CrisWedgeObject p A I γ C (algebraMap A C) hIC hpnil :=
  envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ hIC hpnil hJ E N hN γhat hγhat

/-- The iterated tensor-power presentation remains surjective onto `C`. -/
theorem tensorPowerAlgHom_surjective
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {ι : Type u}
    (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) (n : ℕ) :
    Function.Surjective (tensorPowerAlgHom π n) := sorry

/-- The completed envelope of the `(n + 1)`-fold tensor-power presentation as a
`Cris^∧(C/A)` object. -/
noncomputable def crystallineDnCrisObject
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) (n : ℕ)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (J : Ideal (tensorPowerCarrier A ι n))
    (hJ : J = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJ : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    DividedPowerThickening.CrisWedgeObject p A I γ C (algebraMap A C) hIC hpnil :=
  envelopeCompletedCrisObject p γ (algebraMap A C) (tensorPowerAlgHom π n).toRingHom
    (tensorPowerAlgHom_surjective π hπ n) hIC hpnil hJ E N hN γhat hγhat

/-- The underlying divided-power ring of `crystallineDCrisObject` is the named envelope completion. -/
theorem crystallineDCrisObject_B
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial ι A)) (hJ : J = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    (crystallineDCrisObject p I γ π hπ J hJ hIC hpnil hIJ E N hN γhat hγhat).B =
      envelopeCompletionRing p A (MvPolynomial ι A) I γ J hIJ E N hN γhat := sorry

/-- The underlying divided-power ring of `crystallineDnCrisObject` is the named envelope completion. -/
theorem crystallineDnCrisObject_B
    {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I) {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) (n : ℕ)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C)) (hpnil : IsNilpotent (p : C))
    (J : Ideal (tensorPowerCarrier A ι n))
    (hJ : J = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJ : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A (tensorPowerCarrier A ι n)) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    (crystallineDnCrisObject p I γ π hπ n hIC hpnil J hJ hIJ E N hN γhat hγhat).B =
      envelopeCompletionRing p A (tensorPowerCarrier A ι n) I γ J hIJ E N hN γhat := sorry
