/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReasLib.Algebra.CentralSimple.Basic

/-! # Tensor Product of Central Simple Algebras

The tensor product of two finite-dimensional central simple k-algebras is again
a finite-dimensional central simple k-algebra.

## Main declarations

- `CSA.instIsCentral_tensorProduct` — centrality of tensor product
- `CSA.instIsSimpleRing_tensorProduct` — simplicity of tensor product
- `CSA.tensorProduct` — the tensor product packaged as `CSA k`

## References

- [Stacks Project, Tag 074G](https://stacks.math.columbia.edu/tag/074G)
-/

@[expose] public section

open scoped TensorProduct
open Algebra Algebra.TensorProduct Subalgebra

universe u v w

namespace CSA

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : CSA.{u, w} k)

private theorem map_bot_range_eq_includeRight_range :
    (map (⊥ : Subalgebra k A).val (AlgHom.id k B)).range =
      (includeRight : B →ₐ[k] A ⊗[k] B).range := by
  rw [Algebra.TensorProduct.map_range, AlgHom.range_comp, Subalgebra.range_val,
    Algebra.map_bot, bot_sup_eq]
  simp

instance instIsCentral_tensorProduct : Algebra.IsCentral k (A ⊗[k] B) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    have hxL : x ∈ centralizer k ((includeLeft : A →ₐ[k] A ⊗[k] B).range : Set (A ⊗[k] B)) := by
      intro y hy
      exact hx y
    rw [centralizer_coe_range_includeLeft_eq_center_tensorProduct,
      Algebra.IsCentral.center_eq_bot, map_bot_range_eq_includeRight_range] at hxL
    rcases hxL with ⟨b, rfl⟩
    have hb : b ∈ center k B := by
      rw [Subalgebra.mem_center_iff]
      intro b'
      apply (includeRight : B →ₐ[k] A ⊗[k] B).injective
      simpa using hx (includeRight b')
    rw [Algebra.IsCentral.mem_center_iff] at hb
    rcases hb with ⟨r, rfl⟩
    exact ⟨r, by simp⟩

instance instIsSimpleRing_tensorProduct : IsSimpleRing (A ⊗[k] B) :=
  isSimpleRing_tensorProduct_of_finite_central_left_factor

/-- The tensor product of finite central simple `k`-algebras, packaged as `CSA k`. -/
def tensorProduct : CSA.{u, max v w} k where
  toAlgCat := AlgCat.of k (A ⊗[k] B)

end

end CSA

end
