/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Tensor coordinates for finite product descent

Tensor products of finite product algebras are finite products of the pairwise tensor
products. The inverse maps are the native finite-coordinate sums of tensor inclusions.
The label-product specialization supplies the overlap coordinates used by affine descent
of finite locally constant sheaves.
-/

@[expose] public section
open scoped TensorProduct
noncomputable section
universe u v w a b

namespace Algebra.FiniteProductDescent

variable (R : Type u) [CommRing R]
variable {I : Type v} {J : Type w} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (A : I → Type a) (B : J → Type b)
variable [∀ i, CommRing (A i)] [∀ j, CommRing (B j)]
variable [∀ i, Algebra R (A i)] [∀ j, Algebra R (B j)]

/-- Both finite product indices are made explicit by the native tensor/product equivalences. -/
def tensorEquiv : (∀ i, A i) ⊗[R] (∀ j, B j) ≃ₐ[R] ∀ i, ∀ j, A i ⊗[R] B j :=
  (Algebra.TensorProduct.comm R (∀ i, A i) (∀ j, B j)).trans
    ((Algebra.TensorProduct.piRight R R (∀ j, B j) A).trans
      (AlgEquiv.piCongrRight fun i ↦
        (Algebra.TensorProduct.comm R (∀ j, B j) (A i)).trans
          (Algebra.TensorProduct.piRight R R (A i) B)))

/-- A pure tensor has the original two coordinates at each overlap index. -/
@[simp]
theorem tensorEquiv_tmul (s : ∀ i, A i) (t : ∀ j, B j) (i : I) (j : J) :
    tensorEquiv R A B (s ⊗ₜ[R] t) i j = s i ⊗ₜ[R] t j := rfl

/-- The inverse sends a single pair of coordinates to the tensor of the two coordinate insertions. -/
theorem tensorEquiv_symm_single (i : I) (j : J) (x : A i) (y : B j) :
    (tensorEquiv R A B).symm (Pi.single i (Pi.single j (x ⊗ₜ[R] y))) =
      Pi.single i x ⊗ₜ[R] Pi.single j y := by sorry

variable (n : J → ℕ)

/-- The tensor product with finite local label algebras has actual overlap-label coordinates. -/
def labelTensorEquiv :
    (∀ i, A i) ⊗[R] (∀ j, Fin (n j) → B j) ≃ₐ[R]
      ∀ i, ∀ j, Fin (n j) → A i ⊗[R] B j :=
  (tensorEquiv R A (fun j ↦ Fin (n j) → B j)).trans
    (AlgEquiv.piCongrRight fun i ↦
      AlgEquiv.piCongrRight fun j ↦
        Algebra.TensorProduct.piRight R R (A i) (fun _ : Fin (n j) ↦ B j))

/-- Each overlap-label component is the tensor of the supplied scalar and label value. -/
@[simp]
theorem labelTensorEquiv_tmul (s : ∀ i, A i) (t : ∀ j, Fin (n j) → B j)
    (i : I) (j : J) (k : Fin (n j)) :
    labelTensorEquiv R A B n (s ⊗ₜ[R] t) i j k = s i ⊗ₜ[R] t j k := rfl

/-- The inverse inserts an overlap-label tensor into the corresponding two input factors. -/
theorem labelTensorEquiv_symm_single (i : I) (j : J) (k : Fin (n j)) (x : A i) (y : B j) :
    (labelTensorEquiv R A B n).symm (Pi.single i (Pi.single j (Pi.single k (x ⊗ₜ[R] y)))) =
      Pi.single i x ⊗ₜ[R] Pi.single j (Pi.single k y) := by sorry

end Algebra.FiniteProductDescent
