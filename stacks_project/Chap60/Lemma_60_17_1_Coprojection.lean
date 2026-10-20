/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.TensorProduct.Maps
public import stacks_project.Chap60.«60_17_0_4_TensorPower»

@[expose] public section

universe u

open Algebra.TensorProduct

/-- The coprojection `P → P ⊗_A ⋯ ⊗_A P` sending `f` to `f ⊗ 1 ⊗ ⋯ ⊗ 1`. -/
noncomputable def tensorPowerCoprojection
    (A : Type u) [CommRing A] (ι : Type u) :
    (n : ℕ) → MvPolynomial ι A →ₐ[A] tensorPowerCarrier A ι n
  | 0 => AlgHom.id A (MvPolynomial ι A)
  | n + 1 =>
      let previous := tensorPowerStage A ι n
      -- Local instance justification (defeq pin): recursively stored structures are needed to form the next tensor stage.
      letI : CommRing previous.carrier := previous.commRing
      -- Local instance justification (defeq pin): recursively stored structures are needed to form the next tensor stage.
      letI : Algebra A previous.carrier := previous.algebra
      includeLeft (R := A) (S := A) (A := MvPolynomial ι A) (B := previous.carrier)

/-- The coprojection on a single polynomial copy is the identity. -/
theorem tensorPowerCoprojection_zero
    (A : Type u) [CommRing A] (ι : Type u) :
    tensorPowerCoprojection A ι 0 = AlgHom.id A (MvPolynomial ι A) := rfl

/-- On a successor stage the coprojection is left inclusion into the tensor product. -/
theorem tensorPowerCoprojection_succ
    (A : Type u) [CommRing A] (ι : Type u) (n : ℕ)
    (f : MvPolynomial ι A) :
    tensorPowerCoprojection A ι (n + 1) f =
      (f ⊗ₜ[A] (1 : tensorPowerCarrier A ι n)) := rfl

/-- The embedding of `P` into the chosen tensor factor of the iterated product. -/
noncomputable def tensorPowerSlot
    (A : Type u) [CommRing A] (ι : Type u) :
    (n : ℕ) → Fin (n + 1) → MvPolynomial ι A →ₐ[A] tensorPowerCarrier A ι n
  | 0, _ => AlgHom.id A (MvPolynomial ι A)
  | n + 1, j =>
      let previous := tensorPowerStage A ι n
      -- Local instance justification (defeq pin): recursively stored structures are needed to form the next tensor stage.
      letI : CommRing previous.carrier := previous.commRing
      -- Local instance justification (defeq pin): recursively stored structures are needed to form the next tensor stage.
      letI : Algebra A previous.carrier := previous.algebra
      Fin.cases (includeLeft (R := A) (S := A) (A := MvPolynomial ι A) (B := previous.carrier))
        (fun j0 ↦
          (includeRight (R := A) (A := MvPolynomial ι A) (B := previous.carrier)).comp
            (tensorPowerSlot A ι n j0)) j

/-- Evaluate each tensor factor by its own algebra homomorphism. -/
noncomputable def tensorPowerLiftSlots
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {ι : Type u} :
    (n : ℕ) → (Fin (n + 1) → MvPolynomial ι A →ₐ[A] C) →
      tensorPowerCarrier A ι n →ₐ[A] C
  | 0, f => f 0
  | n + 1, f =>
      Algebra.TensorProduct.productMap (f 0)
        (tensorPowerLiftSlots n (fun j ↦ f j.succ))

/-- The tensor lift evaluates a slot using exactly the homomorphism assigned to it. -/
theorem tensorPowerLiftSlots_slot
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {ι : Type u}
    (n : ℕ) (f : Fin (n + 1) → MvPolynomial ι A →ₐ[A] C)
    (j : Fin (n + 1)) (p : MvPolynomial ι A) :
    tensorPowerLiftSlots n f (tensorPowerSlot A ι n j p) = f j p := by
  induction n with
  | zero =>
      change f 0 p = f j p
      exact congrArg (fun k ↦ f k p) (Subsingleton.elim (0 : Fin 1) j)
  | succ n ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · change Algebra.TensorProduct.productMap (f 0)
          (tensorPowerLiftSlots n (fun k ↦ f k.succ)) (p ⊗ₜ[A] 1) = _
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
      · change Algebra.TensorProduct.productMap (f 0)
          (tensorPowerLiftSlots n (fun k ↦ f k.succ))
          (1 ⊗ₜ[A] tensorPowerSlot A ι n j p) = _
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul, ih]

/-- The zeroth slot is the coprojection `f ↦ f ⊗ 1 ⊗ ⋯ ⊗ 1`. -/
theorem tensorPowerSlot_zero
    (A : Type u) [CommRing A] (ι : Type u) (n : ℕ) :
    tensorPowerSlot A ι n 0 = tensorPowerCoprojection A ι n := by
  cases n <;> rfl

/-- The source elements `ξ_i(j)`: first-slot minus `(j + 1)`-st-slot images of `X i`. -/
noncomputable def crystallineXi
    {A : Type u} [CommRing A] {ι : Type u} (n : ℕ) (i : ι) (j : Fin n) :
    tensorPowerCarrier A ι n :=
  tensorPowerSlot A ι n 0 (MvPolynomial.X i) -
    tensorPowerSlot A ι n j.succ (MvPolynomial.X i)

/-- `ξ_i(j)` is the difference of the coprojection of `X i` and the `(j + 1)`-st slot. -/
theorem crystallineXi_spec
    {A : Type u} [CommRing A] {ι : Type u} (n : ℕ) (i : ι) (j : Fin n) :
    crystallineXi n i j =
      tensorPowerCoprojection A ι n (MvPolynomial.X i) -
        tensorPowerSlot A ι n j.succ (MvPolynomial.X i) := by
  simp only [crystallineXi, tensorPowerSlot_zero]
