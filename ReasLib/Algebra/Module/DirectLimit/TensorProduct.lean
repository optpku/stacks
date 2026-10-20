/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

@[expose] public section

open scoped TensorProduct

universe u v w z

namespace Module.DirectLimit

/-- Tensoring a directed module colimit on the left is equivalent to the colimit of the
corresponding tensor products, with the transition maps induced by left tensoring. -/
noncomputable def tensorProductRight
    {R : Type u} [CommSemiring R]
    {ι : Type v} [DecidableEq ι] [Preorder ι]
    {G : ι → Type w} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
    (M : Type z) [AddCommMonoid M] [Module R M] :
    DirectLimit (fun i ↦ M ⊗[R] G i) (fun i j h ↦ LinearMap.lTensor M (f i j h)) ≃ₗ[R]
      M ⊗[R] DirectLimit G f :=
  (TensorProduct.directLimitRight f M).symm

end Module.DirectLimit
