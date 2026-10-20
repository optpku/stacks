/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.TensorPower
public import ReasLib.RingTheory.DividedPowers.Polynomial
public import ReasLib.RingTheory.DividedPowers.Envelope.Universal

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace DividedPowerEnvelope.TensorPower

variable {A : Type u} [CommRing A] {ι : Type u}
variable {I : Ideal A} {γ : DividedPowers I} {JP : Ideal (MvPolynomial ι A)}
variable {hIJP : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ JP}
variable (EP : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) JP hIJP)

/-- Embed polynomial coefficients into divided-power polynomials over the envelope. -/
def coefficientMap (n : ℕ) : MvPolynomial ι A →+* DPPolynomial EP.D (ι × Fin n) :=
  (algebraMap EP.D (DPPolynomial EP.D (ι × Fin n))).comp EP.toD

/-- The divided-power polynomial ring with its explicitly induced base-algebra structure. -/
def polynomialAlgebra (n : ℕ) : CommAlgCat A :=
  @CommAlgCat.of A _ (DPPolynomial EP.D (ι × Fin n)) _
    (((coefficientMap EP n).comp (algebraMap A (MvPolynomial ι A))).toAlgebra)

/-- The zeroth slot embeds coefficients; a positive slot subtracts its indexed variable. -/
def slotMap (n : ℕ) (j : Fin (n + 1)) : MvPolynomial ι A →ₐ[A] polynomialAlgebra EP n :=
  Fin.cases
    { toRingHom := coefficientMap EP n, commutes' := fun _ ↦ rfl }
    (fun k ↦ MvPolynomial.aeval (fun i ↦
      coefficientMap EP n (MvPolynomial.X i) - DPPolynomial.X EP.D (i, k))) j

/-- Evaluate the canonical finite tensor product in the divided-power polynomial ring. -/
def tensorMap (n : ℕ) : MvPolynomial.TensorPower.carrier A ι n →+* DPPolynomial EP.D (ι × Fin n) :=
  (MvPolynomial.TensorPower.liftSlots A ι n (slotMap EP n)).toRingHom

/-- Evaluation on the zeroth slot is the coefficient embedding. -/
theorem tensorMap_coprojection (n : ℕ) :
    (tensorMap EP n).comp (MvPolynomial.TensorPower.slot A ι n 0).toRingHom =
      coefficientMap EP n := by
  apply RingHom.ext
  intro f
  change MvPolynomial.TensorPower.liftSlots A ι n (slotMap EP n)
    (MvPolynomial.TensorPower.slot A ι n 0 f) = _
  rw [MvPolynomial.TensorPower.liftSlots_slot]
  rfl

/-- Evaluation takes each zeroth-minus-positive coordinate difference to its variable. -/
theorem tensorMap_difference (n : ℕ) (i : ι) (j : Fin n) :
    tensorMap EP n (MvPolynomial.TensorPower.difference A ι i j) =
      DPPolynomial.X EP.D (i, j) := by
  change MvPolynomial.TensorPower.liftSlots A ι n (slotMap EP n)
    (MvPolynomial.TensorPower.slot A ι n 0 (MvPolynomial.X i) -
      MvPolynomial.TensorPower.slot A ι n j.succ (MvPolynomial.X i)) = _
  rw [map_sub, MvPolynomial.TensorPower.liftSlots_slot, MvPolynomial.TensorPower.liftSlots_slot]
  simp only [slotMap, Fin.cases_zero, Fin.cases_succ, MvPolynomial.aeval_X]
  exact sub_sub_cancel _ _

/-- Tensor evaluation respects the divided powers of the base ideal. -/
theorem tensorMap_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism γ (DPPolynomial.dividedPowers EP.D.dividedPowers)
      ((tensorMap EP n).comp (algebraMap A (MvPolynomial.TensorPower.carrier A ι n))) := sorry

variable {C : Type u} [CommRing C] [Algebra A C]
variable (π : MvPolynomial ι A →ₐ[A] C) (hJP : JP = RingHom.ker π.toRingHom)
variable (n : ℕ) {Jn : Ideal (MvPolynomial.TensorPower.carrier A ι n)}
variable (hJn : Jn = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
variable {hIJn : Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ Jn}
variable (En : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) Jn hIJn)

include π hJP hJn in
/-- Tensor evaluation takes the presentation kernel into the extended divided-power ideal. -/
theorem tensorMap_map_ideal :
    Ideal.map (tensorMap EP n) Jn ≤ DPPolynomial.ideal EP.D (ι × Fin n) EP.D.ideal := sorry

variable (hEn : DividedPowerEnvelope.IsUniversal γ
  (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) hIJn En)

/-- The tensor-envelope comparison obtained from its universal divided-power factorization. -/
def toPolynomialDP : En.D ⟶ DividedPowerRing.of (DPPolynomial EP.D (ι × Fin n))
    (DPPolynomial.ideal EP.D (ι × Fin n) EP.D.ideal) (DPPolynomial.dividedPowers EP.D.dividedPowers) :=
  (@hEn (DividedPowerRing.of (DPPolynomial EP.D (ι × Fin n))
    (DPPolynomial.ideal EP.D (ι × Fin n) EP.D.ideal) (DPPolynomial.dividedPowers EP.D.dividedPowers))
    (tensorMap EP n) (tensorMap_isDPMorphism EP n)
    (tensorMap_map_ideal EP π hJP n hJn)).choose

/-- The underlying ring map of the canonical tensor-envelope factorization. -/
def toPolynomial : En.D →+* DPPolynomial EP.D (ι × Fin n) :=
  (toPolynomialDP EP π hJP n hJn En hEn).toRingHom

/-- The envelope comparison factors the specified tensor evaluation map. -/
theorem toPolynomial_comp_toD :
    (toPolynomial EP π hJP n hJn En hEn).comp En.toD = tensorMap EP n := sorry

/-- The envelope comparison is the unique compatible divided-power factorization. -/
theorem toPolynomial_unique
    (f : En.D ⟶ DividedPowerRing.of (DPPolynomial EP.D (ι × Fin n))
      (DPPolynomial.ideal EP.D (ι × Fin n) EP.D.ideal) (DPPolynomial.dividedPowers EP.D.dividedPowers))
    (hf : f.toRingHom.comp En.toD = tensorMap EP n) :
    f = toPolynomialDP EP π hJP n hJn En hEn := sorry

/-- The zeroth-slot presentation map respects the base divided powers. -/
theorem baseToTensor_isDPMorphism :
    DividedPowers.IsDPMorphism γ En.D.dividedPowers
      ((En.toD.comp (MvPolynomial.TensorPower.slot A ι n 0).toRingHom).comp
        (algebraMap A (MvPolynomial ι A))) := sorry

include π hJP hJn in
/-- The zeroth-slot presentation map sends the base presentation kernel into the tensor ideal. -/
theorem baseToTensor_map_ideal :
    Ideal.map (En.toD.comp (MvPolynomial.TensorPower.slot A ι n 0).toRingHom) JP ≤ En.D.ideal := sorry

variable (hEP : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJP EP)

/-- The divided-power map of envelopes induced by the zeroth tensor slot. -/
def baseToTensorDP : EP.D ⟶ En.D :=
  (@hEP En.D (En.toD.comp (MvPolynomial.TensorPower.slot A ι n 0).toRingHom)
    (baseToTensor_isDPMorphism n En) (baseToTensor_map_ideal π hJP n hJn En)).choose

/-- The underlying ring map of the zeroth-slot map of divided-power envelopes. -/
def baseToTensor : EP.D →+* En.D := (baseToTensorDP EP π hJP n hJn En hEP).toRingHom

/-- The base-envelope map factors the zeroth-slot presentation map. -/
theorem baseToTensor_spec :
    (baseToTensor EP π hJP n hJn En hEP).comp EP.toD =
      En.toD.comp (MvPolynomial.TensorPower.slot A ι n 0).toRingHom := sorry

/-- The base-envelope map is unique among compatible divided-power factorizations. -/
theorem baseToTensor_unique (f : EP.D ⟶ En.D)
    (hf : f.toRingHom.comp EP.toD = En.toD.comp (MvPolynomial.TensorPower.slot A ι n 0).toRingHom) :
    f = baseToTensorDP EP π hJP n hJn En hEP := sorry

/-- The tensor-envelope comparison sends the base-envelope map to coefficient inclusion. -/
theorem toPolynomial_comp_baseToTensor :
    (toPolynomial EP π hJP n hJn En hEn).comp (baseToTensor EP π hJP n hJn En hEP) =
      algebraMap EP.D (DPPolynomial EP.D (ι × Fin n)) := sorry

include hEP in
/-- Universal tensor envelopes are identified by the concrete divided-power polynomial map. -/
theorem toPolynomial_bijective :
    Function.Bijective (toPolynomial EP π hJP n hJn En hEn) := sorry

end DividedPowerEnvelope.TensorPower
