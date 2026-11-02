/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Tensor

/-!
# Tensor Products of Extended Ideals

This leaf owns the canonical map from an ideal tensor product to the tensor
product of its extension along an algebra map.  It is independent of flatness
and quotient presentations, so it can be used by base-change, localization,
and fiber arguments directly.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Ideal.Map

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The pure-tensor map induced by `Algebra.idealMap` is additive in the ideal factor. -/
theorem tensor_left_add (I : Ideal R) (x y : I) :
    (TensorProduct.mk S (Ideal.map (algebraMap R S) I) M
      (Algebra.idealMap S I (x + y))).restrictScalars R =
      (TensorProduct.mk S (Ideal.map (algebraMap R S) I) M
        (Algebra.idealMap S I x)).restrictScalars R +
        (TensorProduct.mk S (Ideal.map (algebraMap R S) I) M
          (Algebra.idealMap S I y)).restrictScalars R := by
  ext m
  change Algebra.idealMap S I (x + y) ⊗ₜ[S] m =
    Algebra.idealMap S I x ⊗ₜ[S] m + Algebra.idealMap S I y ⊗ₜ[S] m
  rw [map_add, TensorProduct.add_tmul]

/-- The pure-tensor map induced by `Algebra.idealMap` is `R`-linear in the ideal factor. -/
theorem tensor_left_smul (I : Ideal R) (r : R) (x : I) :
    (TensorProduct.mk S (Ideal.map (algebraMap R S) I) M
      (Algebra.idealMap S I (r • x))).restrictScalars R =
      r • (TensorProduct.mk S (Ideal.map (algebraMap R S) I) M
        (Algebra.idealMap S I x)).restrictScalars R := by
  ext m
  change Algebra.idealMap S I (r • x) ⊗ₜ[S] m =
    r • (Algebra.idealMap S I x ⊗ₜ[S] m)
  rw [map_smul, TensorProduct.smul_tmul']

/-- The canonical `R`-linear map from `I ⊗[R] M` to the tensor product of the extended ideal
with `M` over `S`. -/
@[stacks 0523 "mapped ideal tensor transport"]
noncomputable def tensor (I : Ideal R) :
    I ⊗[R] M →ₗ[R] Ideal.map (algebraMap R S) I ⊗[S] M :=
  TensorProduct.lift
    { toFun := fun x ↦
        (TensorProduct.mk S (Ideal.map (algebraMap R S) I) M
          (Algebra.idealMap S I x)).restrictScalars R
      map_add' := tensor_left_add (S := S) (M := M) I
      map_smul' := tensor_left_smul (S := S) (M := M) I }

/-- `Ideal.Map.tensor` sends a pure tensor to the pure tensor of the extended ideal element. -/
@[simp, stacks 0523 "mapped ideal tensor transport"]
theorem tensor_tmul (I : Ideal R) (x : I) (m : M) :
    tensor (S := S) (M := M) I (x ⊗ₜ[R] m) = Algebra.idealMap S I x ⊗ₜ[S] m := by
  rfl

/-- The canonical map from an ideal tensor product to the tensor product of its extension is
surjective. -/
@[stacks 0523 "mapped ideal tensor transport"]
theorem tensor_surjective (I : Ideal R) :
    Function.Surjective (tensor (S := S) (M := M) I) := by
  have h : ∀ (y : S) (hy : y ∈ Ideal.map (algebraMap R S) I) (m : M),
      ∃ x, tensor (S := S) (M := M) I x =
        (⟨y, hy⟩ : Ideal.map (algebraMap R S) I) ⊗ₜ[S] m := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro m
      exact ⟨(⟨a, ha⟩ : I) ⊗ₜ[R] m, tensor_tmul I ⟨a, ha⟩ m⟩
    | zero =>
      intro m
      refine ⟨0, ?_⟩
      change tensor (S := S) (M := M) I 0 =
        (0 : Ideal.map (algebraMap R S) I) ⊗ₜ[S] m
      simp
    | add y z hy hz ihy ihz =>
      intro m
      obtain ⟨a, ha⟩ := ihy m
      obtain ⟨b, hb⟩ := ihz m
      refine ⟨a + b, ?_⟩
      rw [map_add, ha, hb]
      exact (TensorProduct.add_tmul
        (⟨y, hy⟩ : Ideal.map (algebraMap R S) I) ⟨z, hz⟩ m).symm
    | smul s y hy ih =>
      intro m
      -- Move the coefficient in the extended ideal to the module factor.
      obtain ⟨a, ha⟩ := ih (s • m)
      exact ⟨a, ha.trans (TensorProduct.smul_tmul s
        (⟨y, hy⟩ : Ideal.map (algebraMap R S) I) m).symm⟩
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul y m => exact h y y.2 m
  | add y z ihy ihz =>
    obtain ⟨a, rfl⟩ := ihy
    obtain ⟨b, rfl⟩ := ihz
    exact ⟨a + b, map_add _ _ _⟩

/-- The tensor map induced by extending an ideal sends the `I`-power filtration of the source
tensor product into the corresponding power filtration of the extended ideal. -/
@[stacks 0523 "mapped ideal tensor power filtration"]
theorem tensor_mem_pow_smul_top (I : Ideal R) (n : ℕ) {x : I ⊗[R] M}
    (hx : x ∈ I ^ n • (⊤ : Submodule R (I ⊗[R] M))) :
    tensor (S := S) (M := M) I x ∈
      (Ideal.map (algebraMap R S) I) ^ n •
        (⊤ : Submodule S (Ideal.map (algebraMap R S) I ⊗[S] M)) := by
  change tensor (S := S) (M := M) I x ∈
    (((Ideal.map (algebraMap R S) I) ^ n •
      (⊤ : Submodule S (Ideal.map (algebraMap R S) I ⊗[S] M))).restrictScalars R)
  rw [← Ideal.map_pow, Ideal.smul_restrictScalars]
  exact Submodule.smul_top_le_comap_smul_top (I ^ n)
    (tensor (S := S) (M := M) I) hx

/-- Ideal tensor multiplication commutes with extension of the ideal along an algebra map. -/
@[stacks 0523 "mapped ideal tensor multiplication"]
theorem tensorMul_comp (I : Ideal R) :
    ((Ideal.map (algebraMap R S) I).tensorMul M).restrictScalars R ∘ₗ
        tensor (S := S) (M := M) I =
      I.tensorMul M := by
  apply TensorProduct.ext'
  intro x m
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, tensor_tmul,
    Ideal.tensorMul_tmul]
  exact algebraMap_smul S x.1 m

/-- Injectivity of ideal tensor multiplication descends along extension of the ideal. -/
@[stacks 0523 "mapped ideal tensor injectivity"]
theorem tensorMul_injective (I : Ideal R)
    (h : Function.Injective (I.tensorMul M)) :
    Function.Injective ((Ideal.map (algebraMap R S) I).tensorMul M) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := tensor_surjective (S := S) (M := M) I x
  obtain ⟨b, rfl⟩ := tensor_surjective (S := S) (M := M) I y
  apply congrArg (tensor (S := S) (M := M) I)
  apply h
  change (((Ideal.map (algebraMap R S) I).tensorMul M).restrictScalars R ∘ₗ
    tensor (S := S) (M := M) I) a =
    (((Ideal.map (algebraMap R S) I).tensorMul M).restrictScalars R ∘ₗ
      tensor (S := S) (M := M) I) b at hxy
  rwa [tensorMul_comp] at hxy

end Ideal.Map
