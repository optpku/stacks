/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
          (Algebra.idealMap S I y)).restrictScalars R := sorry

/-- The pure-tensor map induced by `Algebra.idealMap` is `R`-linear in the ideal factor. -/
theorem tensor_left_smul (I : Ideal R) (r : R) (x : I) :
    (TensorProduct.mk S (Ideal.map (algebraMap R S) I) M
      (Algebra.idealMap S I (r • x))).restrictScalars R =
      r • (TensorProduct.mk S (Ideal.map (algebraMap R S) I) M
        (Algebra.idealMap S I x)).restrictScalars R := sorry

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
    tensor (S := S) (M := M) I (x ⊗ₜ[R] m) = Algebra.idealMap S I x ⊗ₜ[S] m := sorry

/-- The canonical map from an ideal tensor product to the tensor product of its extension is
surjective. -/
@[stacks 0523 "mapped ideal tensor transport"]
theorem tensor_surjective (I : Ideal R) :
    Function.Surjective (tensor (S := S) (M := M) I) := sorry

/-- The tensor map induced by extending an ideal sends the `I`-power filtration of the source
tensor product into the corresponding power filtration of the extended ideal. -/
@[stacks 0523 "mapped ideal tensor power filtration"]
theorem tensor_mem_pow_smul_top (I : Ideal R) (n : ℕ) {x : I ⊗[R] M}
    (hx : x ∈ I ^ n • (⊤ : Submodule R (I ⊗[R] M))) :
    tensor (S := S) (M := M) I x ∈
      (Ideal.map (algebraMap R S) I) ^ n •
        (⊤ : Submodule S (Ideal.map (algebraMap R S) I ⊗[S] M)) := sorry

/-- Ideal tensor multiplication commutes with extension of the ideal along an algebra map. -/
@[stacks 0523 "mapped ideal tensor multiplication"]
theorem tensorMul_comp (I : Ideal R) :
    ((Ideal.map (algebraMap R S) I).tensorMul M).restrictScalars R ∘ₗ
        tensor (S := S) (M := M) I =
      I.tensorMul M := sorry

/-- Injectivity of ideal tensor multiplication descends along extension of the ideal. -/
@[stacks 0523 "mapped ideal tensor injectivity"]
theorem tensorMul_injective (I : Ideal R)
    (h : Function.Injective (I.tensorMul M)) :
    Function.Injective ((Ideal.map (algebraMap R S) I).tensorMul M) := sorry

end Ideal.Map
