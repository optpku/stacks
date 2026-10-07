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

/-- Map every factor through the same polynomial presentation. -/
noncomputable def diagonal {R : Type u} [CommRing R] [Algebra A R]
    (π : MvPolynomial ι A →ₐ[A] R) (n : ℕ) : carrier A ι n →ₐ[A] R :=
  liftSlots A ι n (fun _ ↦ π)

/-- The zeroth polynomial coordinate minus its copy in a positive slot. -/
noncomputable def difference {n : ℕ} (i : ι) (j : Fin n) : carrier A ι n :=
  slot A ι n 0 (MvPolynomial.X i) - slot A ι n j.succ (MvPolynomial.X i)

end MvPolynomial.TensorPower
