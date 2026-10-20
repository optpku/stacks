/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.BrauerGroup.Defs

/-! # Scalar Extension of Central Simple Algebras

Scalar extension of a finite-dimensional central simple k-algebra along a field
extension k'/k yields a central simple k'-algebra.

## Main declarations

- `CSA.instIsCentral_baseChange` — centrality of the base change
- `CSA.instIsSimpleRing_baseChange` — simplicity of the base change
- `CSA.baseChange` — the scalar extension packaged as `CSA k'`

## References

- [Stacks Project, Tag 074H](https://stacks.math.columbia.edu/tag/074H)
-/

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace CSA

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, w} k)
variable (k' : Type v) [Field k'] [Algebra k k']

private theorem map_bot_range_eq_includeLeft_range :
    (Algebra.TensorProduct.map (AlgHom.id k k') (⊥ : Subalgebra k A).val).range =
      (includeLeft : k' →ₐ[k] k' ⊗[k] A).range := by
  rw [Algebra.TensorProduct.map_range]
  have hbot :
      ((includeRight : A →ₐ[k] k' ⊗[k] A).comp (⊥ : Subalgebra k A).val).range =
        (⊥ : Subalgebra k (k' ⊗[k] A)) := by
    rw [AlgHom.range_comp, Subalgebra.range_val, Algebra.map_bot]
  rw [hbot, sup_bot_eq]
  simp

/-- The scalar extension of a central simple algebra remains central over the larger field. -/
instance instIsCentral_baseChange : Algebra.IsCentral k' (k' ⊗[k] A) := by
  refine ⟨fun x hx ↦ ?_⟩
  have hx' :
      x ∈ Subalgebra.centralizer k
        (includeRight : A →ₐ[k] k' ⊗[k] A).range := by
    rw [Subalgebra.mem_centralizer_iff]
    rw [Subalgebra.mem_center_iff] at hx
    intro y _
    exact hx y
  have hx'' :
      x ∈ (Algebra.TensorProduct.map (AlgHom.id k k') (Subalgebra.center k A).val).range := by
    rwa [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct k k' A] at hx'
  have hx''' : x ∈ (includeLeft : k' →ₐ[k] k' ⊗[k] A).range := by
    rw [Algebra.IsCentral.center_eq_bot, map_bot_range_eq_includeLeft_range A k'] at hx''
    exact hx''
  rcases hx''' with ⟨y, rfl⟩
  exact Subalgebra.algebraMap_mem (⊥ : Subalgebra k' (k' ⊗[k] A)) y

/-- The scalar extension of a finite central simple algebra remains a simple ring. -/
instance instIsSimpleRing_baseChange : IsSimpleRing (k' ⊗[k] A) := by
  exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A k').toRingEquiv
    isSimpleRing_tensorProduct_of_finite_central_left_factor

/-- Scalar extension of a finite central simple `k`-algebra along a field extension,
packaged as `CSA k'`. -/
noncomputable def baseChange : CSA k' :=
  CSA.mk (AlgCat.of k' (k' ⊗[k] A))

end

end CSA

end
