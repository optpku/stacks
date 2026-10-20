/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.TensorPowerCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 60.17.1 -/
@[stacks 07L2] #check (DividedPowerEnvelope.TensorPower.polynomialCompletionIso :
  ∀ {A : Type u} [CommRing A]
    (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I)
    {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π)
    (JP : Ideal (MvPolynomial ι A)) (hJP : JP = RingHom.ker π.toRingHom)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (hpnil : IsNilpotent (p : C))
    (hIJP : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ JP)
    (EP : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) JP hIJP)
    (hEP : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJP EP)
    (n : ℕ) (Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn)
    (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En),
    DividedPowerEnvelope.TensorPower.sourceAlgebra p EP π hJP n hJn En hEP ≅
      DividedPowerEnvelope.TensorPower.targetAlgebra p EP n)

open DividedPowerEnvelope.TensorPower


variable {A : Type u} [CommRing A] {ι : Type u}
variable {I : Ideal A} {γ : DividedPowers I} {JP : Ideal (MvPolynomial ι A)}
variable {hIJP : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ JP}
variable (p : ℕ)
variable (EP : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) JP hIJP)
variable {C : Type u} [CommRing C] [Algebra A C]
variable (π : MvPolynomial ι A →ₐ[A] C) (hJP : JP = RingHom.ker π.toRingHom)
variable (n : ℕ) {Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n)}
variable (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
variable {hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn}
variable (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)
variable (hEn : DividedPowerEnvelope.IsUniversal γ
  (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)
variable (hEP : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJP EP)


#check (polynomialCompletionIso_coprojection p EP π hJP n hJn En hEn hEP :
  ∀ (f : MvPolynomial ι A),
    (polynomialCompletionIsoCore p EP π hJP n hJn En hEn hEP).hom.hom
      (AdicCompletion.of _ En.D (En.toD (MvPolynomial.TensorPower.slot A ι n 0 f))) =
    AdicCompletion.of _ (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n))
      (algebraMap (AdicCompletion.Nat.ring p EP.D)
        (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n))
        (AdicCompletion.of _ EP.D (EP.toD f))))

#check (polynomialCompletionIso_difference p EP π hJP n hJn En hEn hEP :
  ∀ (i : ι) (j : Fin n),
    (polynomialCompletionIsoCore p EP π hJP n hJn En hEn hEP).hom.hom
      (AdicCompletion.of _ En.D (En.toD (MvPolynomial.TensorPower.difference A ι i j))) =
    AdicCompletion.of _ (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n))
      (DPPolynomial.X (AdicCompletion.Nat.ring p EP.D) (i, j)))
