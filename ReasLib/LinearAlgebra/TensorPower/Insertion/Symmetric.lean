module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import ReasLib.LinearAlgebra.TensorPower.Insertion.Slots

/-!
# Symmetric-power relations from tensor-slot insertion

This leaf owns the commutator presentation of symmetric powers.  Its
subtraction-bearing assumptions do not leak into the common slot API.

@stack 00DP
-/

@[expose] public section

open scoped TensorProduct
open PiTensorProduct

universe u v w

namespace TensorPower.Insertion.Symmetric

section Relations

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Type w}

/-- The commutator relation map attached to a family of generators. -/
@[stacks 00DP "canonical symmetric commutator relation map"]
noncomputable def commutatorMap (n : ℕ) (x : I → M) :
    (SlotPair n × I × I) → ⨂[R]^(n - 2) M →ₗ[R] ⨂[R]^n M
  | ⟨p, i₁, i₂⟩ =>
      twoSlotMap n p (x i₁) (x i₂) - twoSlotMap n p (x i₂) (x i₁)

/-- The direct-sum source for the symmetric relation map. -/
@[stacks 00DP "canonical symmetric relation source"]
abbrev Source (R : Type u) (M : Type v) (n : ℕ) (I : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] :=
  (SlotPair n × I × I) →₀ ⨂[R]^(n - 2) M

/-- The family-level symmetric relation map. -/
@[stacks 00DP]
noncomputable def relationMap (n : ℕ) (x : I → M) :
    Source R M n I →ₗ[R] ⨂[R]^n M :=
  Finsupp.lsum R (fun a ↦ commutatorMap n x a)

/-- The symmetric relation map on one commutator summand. -/
@[simp]
theorem relationMap_single (n : ℕ) (x : I → M)
    (p : SlotPair n) (i₁ i₂ : I) (z : ⨂[R]^(n - 2) M) :
    relationMap n x (Finsupp.single (p, i₁, i₂) z) =
      twoSlotMap n p (x i₁) (x i₂) z -
        twoSlotMap n p (x i₂) (x i₁) z := by
  simp [relationMap, commutatorMap]

/-- Pure-tensor formula for a commutator generator. -/
theorem relationMap_tprod (n : ℕ) (x : I → M)
    (p : SlotPair n) (i₁ i₂ : I) (m : Fin (n - 2) → M) :
    relationMap n x (Finsupp.single (p, i₁, i₂) (tprod R m)) =
      tprod R (insert n p (x i₁) (x i₂) m) -
        tprod R (insert n p (x i₂) (x i₁) m) := by
  rw [relationMap_single, twoSlotMap_tprod, twoSlotMap_tprod]

end Relations

section Kernel

variable {R : Type} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Type w}

/-- A spanning family's symmetric relation map is exactly the canonical kernel. -/
@[stacks 00DP]
theorem generator_ker_eq_range (n : ℕ) (x : I → M)
    (hx : Submodule.span R (Set.range x) = ⊤) :
    LinearMap.ker (SymmetricPower.mk R (Fin n) M) =
      LinearMap.range (relationMap n x) := sorry

/-- Exactness part of the symmetric generator presentation. -/
theorem generator_exact (n : ℕ) (x : I → M)
    (hx : Submodule.span R (Set.range x) = ⊤) :
    Function.Exact (relationMap n x)
      (SymmetricPower.mk R (Fin n) M) := sorry

/-- The canonical tensor-to-symmetric map is surjective. -/
theorem generator_surjective (n : ℕ) :
    Function.Surjective (SymmetricPower.mk R (Fin n) M) := sorry

/-- A spanning family gives an exact presentation of the symmetric power. -/
@[stacks 00DP]
theorem generator_exact_sequence (n : ℕ) (x : I → M)
    (hx : Submodule.span R (Set.range x) = ⊤) :
    Function.Exact (relationMap n x)
        (SymmetricPower.mk R (Fin n) M) ∧
      Function.Surjective (SymmetricPower.mk R (Fin n) M) := sorry

end Kernel

end TensorPower.Insertion.Symmetric
