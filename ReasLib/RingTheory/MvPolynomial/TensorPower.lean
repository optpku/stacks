/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

universe u

namespace MvPolynomial.TensorPower

variable (A : Type u) [CommRing A] (ι : Type u)

/-- The tensor product of the polynomial algebra with one factor for each slot. -/
abbrev carrier (n : ℕ) := PiTensorProduct A (fun _ : Fin (n + 1) ↦ MvPolynomial ι A)

/-- The inclusion of a polynomial factor in its designated tensor slot. -/
noncomputable def slot (n : ℕ) (j : Fin (n + 1)) :
    MvPolynomial ι A →ₐ[A] carrier A ι n :=
  PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (n + 1) ↦ MvPolynomial ι A) j

/-- The multiplicative multilinear map underlying evaluation of all tensor factors. -/
noncomputable def liftMap {R : Type u} [CommRing R] [Algebra A R]
    (n : ℕ) (f : Fin (n + 1) → MvPolynomial ι A →ₐ[A] R) :
    MultilinearMap A (fun _ : Fin (n + 1) ↦ MvPolynomial ι A) R :=
  (MultilinearMap.mkPiAlgebra A (Fin (n + 1)) R).compLinearMap (fun j ↦ (f j).toLinearMap)

/-- The evaluation multilinear map preserves the tensor unit. -/
theorem liftSlots_one {R : Type u} [CommRing R] [Algebra A R]
    (n : ℕ) (f : Fin (n + 1) → MvPolynomial ι A →ₐ[A] R) :
    liftMap A ι n f 1 = 1 := by simp [liftMap]

/-- The evaluation multilinear map preserves multiplication of pure tensors. -/
theorem liftSlots_mul {R : Type u} [CommRing R] [Algebra A R]
    (n : ℕ) (f : Fin (n + 1) → MvPolynomial ι A →ₐ[A] R)
    (x y : Fin (n + 1) → MvPolynomial ι A) :
    liftMap A ι n f (x * y) = liftMap A ι n f x * liftMap A ι n f y := by
  simp [liftMap, Finset.prod_mul_distrib]

/-- Evaluate the tensor product using one specified algebra homomorphism per slot. -/
noncomputable def liftSlots {R : Type u} [CommRing R] [Algebra A R]
    (n : ℕ) (f : Fin (n + 1) → MvPolynomial ι A →ₐ[A] R) : carrier A ι n →ₐ[A] R :=
  PiTensorProduct.liftAlgHom (liftMap A ι n f) (liftSlots_one A ι n f)
    (liftSlots_mul A ι n f)

/-- Evaluation of a slot agrees with the assigned polynomial evaluation. -/
theorem liftSlots_slot {R : Type u} [CommRing R] [Algebra A R]
    (n : ℕ) (f : Fin (n + 1) → MvPolynomial ι A →ₐ[A] R)
    (j : Fin (n + 1)) (x : MvPolynomial ι A) :
    liftSlots A ι n f (slot A ι n j x) = f j x := sorry

/-- Reindex tensor factors along a map of slots. -/
noncomputable def reindex (n m : ℕ) (σ : Fin (n + 1) → Fin (m + 1)) :
    carrier A ι n →ₐ[A] carrier A ι m :=
  liftSlots A ι n (fun j ↦ slot A ι m (σ j))

/-- Reindexing carries each polynomial slot to its designated target slot. -/
theorem reindex_slot (n m : ℕ) (σ : Fin (n + 1) → Fin (m + 1))
    (j : Fin (n + 1)) (x : MvPolynomial ι A) :
    reindex A ι n m σ (slot A ι n j x) = slot A ι m (σ j) x := sorry

/-- Reindexing by the identity fixes the tensor product. -/
theorem reindex_id (n : ℕ) :
    reindex A ι n n id = AlgHom.id A (carrier A ι n) := sorry

/-- Successive reindexings agree with reindexing by the composite slot map. -/
theorem reindex_comp (n m k : ℕ) (σ : Fin (n + 1) → Fin (m + 1))
    (τ : Fin (m + 1) → Fin (k + 1)) :
    (reindex A ι m k τ).comp (reindex A ι n m σ) =
      reindex A ι n k (τ ∘ σ) := sorry

/-- Map every factor through the same polynomial presentation. -/
noncomputable def diagonal {R : Type u} [CommRing R] [Algebra A R]
    (π : MvPolynomial ι A →ₐ[A] R) (n : ℕ) : carrier A ι n →ₐ[A] R :=
  liftSlots A ι n (fun _ ↦ π)

/-- The diagonal presentation evaluates each polynomial slot by the original presentation. -/
theorem diagonal_slot {R : Type u} [CommRing R] [Algebra A R]
    (π : MvPolynomial ι A →ₐ[A] R) (n : ℕ) (j : Fin (n + 1))
    (polynomial : MvPolynomial ι A) :
    diagonal A ι π n (slot A ι n j polynomial) = π polynomial :=
  liftSlots_slot A ι n (fun _ ↦ π) j polynomial

/-- A surjective polynomial presentation induces a surjective diagonal tensor presentation. -/
theorem diagonal_surjective {R : Type u} [CommRing R] [Algebra A R]
    (π : MvPolynomial ι A →ₐ[A] R) (hπ : Function.Surjective π) (n : ℕ) :
    Function.Surjective (diagonal A ι π n) := by
  intro value
  obtain ⟨polynomial, hpolynomial⟩ := hπ value
  exact ⟨slot A ι n 0 polynomial, (diagonal_slot A ι π n 0 polynomial).trans hpolynomial⟩

/-- The zeroth polynomial coordinate minus its copy in a positive slot. -/
noncomputable def difference {n : ℕ} (i : ι) (j : Fin n) : carrier A ι n :=
  slot A ι n 0 (MvPolynomial.X i) - slot A ι n j.succ (MvPolynomial.X i)

end MvPolynomial.TensorPower
