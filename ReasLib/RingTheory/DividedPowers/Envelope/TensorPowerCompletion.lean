/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.TensorPower
public import ReasLib.RingTheory.DividedPowers.Polynomial.Completion
public import ReasLib.RingTheory.Localization.AtPrime.Int

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace DividedPowerEnvelope.TensorPower

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

/-- The completed tensor envelope with scalar action induced by the completed zeroth-slot map. -/
def sourceAlgebra : CommAlgCat (AdicCompletion.Nat.ring p EP.D) :=
  @CommAlgCat.of (AdicCompletion.Nat.ring p EP.D) _ (AdicCompletion.Nat.ring p En.D) _
    (AdicCompletion.Nat.map p (baseToTensor EP π hJP n hJn En hEP)).toAlgebra

/-- Completed divided-power polynomials over the completed base envelope, with coefficient action. -/
def targetAlgebra : CommAlgCat (AdicCompletion.Nat.ring p EP.D) :=
  CommAlgCat.of (AdicCompletion.Nat.ring p EP.D)
    (AdicCompletion.Nat.ring p (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n)))

/-- Complete the envelope comparison and then complete extension of the coefficient ring. -/
def comparison : AdicCompletion.Nat.ring p En.D →+*
    AdicCompletion.Nat.ring p (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n)) :=
  (DPPolynomial.Completion.comparison p EP.D (ι × Fin n)).comp
    (AdicCompletion.Nat.map p (toPolynomial EP π hJP n hJn En hEn))

/-- The concrete composite intertwines the completed zeroth-slot and coefficient scalar maps. -/
theorem comparison_commutes :
    (comparison p EP π hJP n hJn En hEn).comp
      (AdicCompletion.Nat.map p (baseToTensor EP π hJP n hJn En hEP)) =
    algebraMap (AdicCompletion.Nat.ring p EP.D)
      (AdicCompletion.Nat.ring p (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n))) := sorry

include hEP in
/-- The constructed comparison is bijective for universal base and tensor envelopes. -/
theorem comparison_bijective :
    Function.Bijective (comparison p EP π hJP n hJn En hEn) :=
  (DPPolynomial.Completion.comparison_bijective p EP.D (ι × Fin n)).comp
    (AdicCompletion.Nat.map_bijective p (toPolynomial EP π hJP n hJn En hEn)
      (toPolynomial_bijective EP π hJP n hJn En hEn hEP))

/-- The concrete completed comparison bundled as a homomorphism over the completed base. -/
def comparisonHom : sourceAlgebra p EP π hJP n hJn En hEP ⟶ targetAlgebra p EP n :=
  let f : sourceAlgebra p EP π hJP n hJn En hEP →ₐ[AdicCompletion.Nat.ring p EP.D]
      targetAlgebra p EP n :=
    { toRingHom := comparison p EP π hJP n hJn En hEn
      commutes' := fun r ↦ congrArg (fun f : AdicCompletion.Nat.ring p EP.D →+* _ ↦ f r)
        (comparison_commutes p EP π hJP n hJn En hEn hEP) }
  @CommAlgCat.ofHom (AdicCompletion.Nat.ring p EP.D) _
    (sourceAlgebra p EP π hJP n hJn En hEP) (targetAlgebra p EP n)
    _ (CommAlgCat.algebra (sourceAlgebra p EP π hJP n hJn En hEP))
    _ (CommAlgCat.algebra (targetAlgebra p EP n)) f

/-- The specified envelope comparison gives an isomorphism over the completed base ring. -/
def polynomialCompletionIsoCore :
    sourceAlgebra p EP π hJP n hJn En hEP ≅ targetAlgebra p EP n :=
  let S := sourceAlgebra p EP π hJP n hJn En hEP
  let T := targetAlgebra p EP n
  @CommAlgCat.isoMk (AdicCompletion.Nat.ring p EP.D) _ S T _ _
    (CommAlgCat.algebra S) (CommAlgCat.algebra T)
    (@AlgEquiv.ofBijective (AdicCompletion.Nat.ring p EP.D) S T _ _ _
      (CommAlgCat.algebra S) (CommAlgCat.algebra T)
      (comparisonHom p EP π hJP n hJn En hEn hEP).hom
      (comparison_bijective p EP π hJP n hJn En hEn hEP))

/-- On a zeroth-slot polynomial, the completed isomorphism is completed coefficient inclusion. -/
theorem polynomialCompletionIso_coprojection (f : MvPolynomial ι A) :
    (polynomialCompletionIsoCore p EP π hJP n hJn En hEn hEP).hom.hom
      (AdicCompletion.of _ En.D (En.toD (MvPolynomial.TensorPower.slot A ι n 0 f))) =
    AdicCompletion.of _ (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n))
      (algebraMap (AdicCompletion.Nat.ring p EP.D)
        (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n))
        (AdicCompletion.of _ EP.D (EP.toD f))) := sorry

/-- The completed comparison carries zeroth-minus-positive coordinates to their indexed variables. -/
theorem polynomialCompletionIso_difference (i : ι) (j : Fin n) :
    (polynomialCompletionIsoCore p EP π hJP n hJn En hEn hEP).hom.hom
      (AdicCompletion.of _ En.D (En.toD (MvPolynomial.TensorPower.difference A ι i j))) =
    AdicCompletion.of _ (DPPolynomial (AdicCompletion.Nat.ring p EP.D) (ι × Fin n))
      (DPPolynomial.X (AdicCompletion.Nat.ring p EP.D) (i, j)) := sorry

end DividedPowerEnvelope.TensorPower

/-- The crystalline polynomial-presentation comparison with its full original domain and
the canonical completed zeroth-slot and coefficient algebra structures. -/
noncomputable def DividedPowerEnvelope.TensorPower.polynomialCompletionIso
    {A : Type u} [CommRing A]
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
    (hEn : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En) :
    DividedPowerEnvelope.TensorPower.sourceAlgebra p EP π hJP n hJn En hEP ≅
      DividedPowerEnvelope.TensorPower.targetAlgebra p EP n :=
  DividedPowerEnvelope.TensorPower.polynomialCompletionIsoCore p EP π hJP n hJn En hEn hEP
