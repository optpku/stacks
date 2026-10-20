/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DirectLimit.TensorProduct
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w z

/- Exercise 111.2.7: for a directed system of `A`-modules `N i` with transition maps `φ`
and another `A`-module `M`, tensoring on the left with `M` commutes with the directed
colimit:
`M ⊗[A] Module.DirectLimit N φ ≃ₗ[A] Module.DirectLimit (fun i ↦ M ⊗[A] N i)`.
The source writes the inverse orientation `(TensorProduct.directLimitRight φ M).symm`. -/
@[stacks 02CO]
#check (Module.DirectLimit.tensorProductRight :
  ∀ {R : Type u} [CommSemiring R]
    {ι : Type v} [DecidableEq ι] [Preorder ι]
    {G : ι → Type w} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) (M : Type z) [AddCommMonoid M] [Module R M],
    Module.DirectLimit (fun i ↦ M ⊗[R] G i)
        (fun i j h ↦ LinearMap.lTensor M (f i j h)) ≃ₗ[R]
      M ⊗[R] Module.DirectLimit G f)
