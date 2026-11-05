/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Pi

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

/-- The canonical decomposition of the tensor square of a product algebra into its
four pairwise tensor factors. -/
noncomputable def prodTensorSquare (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂] :
    (B₁ × B₂) ⊗[A] (B₁ × B₂) ≃ₐ[A]
      ((B₁ ⊗[A] B₁) × (B₁ ⊗[A] B₂)) × ((B₂ ⊗[A] B₁) × (B₂ ⊗[A] B₂)) :=
  (prodRight A A (B₁ × B₂) B₁ B₂).trans
    (AlgEquiv.prodCongr
      ((Algebra.TensorProduct.comm A (B₁ × B₂) B₁).trans (prodRight A A B₁ B₁ B₂))
      ((Algebra.TensorProduct.comm A (B₁ × B₂) B₂).trans (prodRight A A B₂ B₁ B₂)))

/-- The four-factor decomposition sends a pure tensor to its four pairwise tensor
components, with the second input supplying the first tensor factor. -/
theorem prodTensorSquare_tmul (A : Type u) (B₁ : Type v) (B₂ : Type w)
    [CommRing A] [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    (b₁ c₁ : B₁) (b₂ c₂ : B₂) :
    prodTensorSquare A B₁ B₂ ((b₁, b₂) ⊗ₜ[A] (c₁, c₂)) =
      ((c₁ ⊗ₜ[A] b₁, c₁ ⊗ₜ[A] b₂), (c₂ ⊗ₜ[A] b₁, c₂ ⊗ₜ[A] b₂)) := by
  simp [prodTensorSquare, prodRight_tmul]

end Algebra.TensorProduct
