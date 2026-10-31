/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Differential Operators Between Modules

This file owns the scalar-commutator calculus for linear maps between modules.
The recursive order predicate only uses a scalar action commuting with the base
ring action.  The later `S`-submodule packaging adds precisely the hypotheses
needed for the output-side scalar action to preserve that predicate.
-/

universe u v w w'

namespace LinearMap

section ScalarCommutator

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w'}
variable [Semiring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [DistribSMul S M] [DistribSMul S N]
variable [SMulCommClass S R M] [SMulCommClass S R N]

/-- The scalar commutator of an `R`-linear map with multiplication by `g : S`. -/
abbrev scalarCommutator (D : M →ₗ[R] N) (g : S) : M →ₗ[R] N :=
  D.comp (DistribSMul.toLinearMap R M g) - (DistribSMul.toLinearMap R N g).comp D

/-- Evaluating a scalar commutator gives `D (g • m) - g • D m`. -/
@[simp]
theorem scalarCommutator_apply (D : M →ₗ[R] N) (g : S) (m : M) :
    D.scalarCommutator g m = D (g • m) - g • D m := rfl

end ScalarCommutator

section OrderPredicate

variable {R : Type u} {M : Type w} {N : Type w'}
variable [Semiring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- An `R`-linear map has differential-operator order at most `k` relative to the scalar
action of `S` if its scalar commutators recursively have order at most `k - 1`. -/
@[stacks 09CI]
def IsDifferentialOperatorOfOrder (D : M →ₗ[R] N) (S : Type v)
    [DistribSMul S M] [DistribSMul S N] [SMulCommClass S R M] [SMulCommClass S R N] :
    ℕ → Prop
  | 0 => ∀ g : S, D.scalarCommutator g = 0
  | k + 1 => ∀ g : S, (D.scalarCommutator g).IsDifferentialOperatorOfOrder S k

end OrderPredicate

section OrderComputation

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w'}
variable [Semiring R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [DistribSMul S M] [DistribSMul S N]
variable [SMulCommClass S R M] [SMulCommClass S R N]

/-- Order-zero differential operators are exactly the maps commuting with the `S`-action. -/
theorem isDifferentialOperatorOfOrder_zero_iff (D : M →ₗ[R] N) :
    D.IsDifferentialOperatorOfOrder S 0 ↔
      ∀ g : S, ∀ m : M, D (g • m) = g • D m := by
  constructor
  · intro h g m
    have hm := congrArg (fun E : M →ₗ[R] N => E m) (h g)
    simpa only [scalarCommutator_apply, zero_apply, sub_eq_zero] using hm
  · intro h g
    apply LinearMap.ext
    intro m
    simpa only [scalarCommutator_apply, zero_apply, sub_eq_zero] using h g m

/-- The successor clause in the recursive definition of differential-operator order. -/
theorem isDifferentialOperatorOfOrder_succ_iff (D : M →ₗ[R] N) (k : ℕ) :
    D.IsDifferentialOperatorOfOrder S (k + 1) ↔
      ∀ g : S, (D.scalarCommutator g).IsDifferentialOperatorOfOrder S k := Iff.rfl

end OrderComputation

section OrderClosure

variable {R : Type u} {S : Type v} {L : Type w} {M : Type w'} {N : Type*}
variable [Semiring R]
variable [AddCommGroup L] [Module R L] [DistribSMul S L] [SMulCommClass S R L]
variable [AddCommGroup M] [Module R M] [DistribSMul S M] [SMulCommClass S R M]
variable [AddCommGroup N] [Module R N] [DistribSMul S N] [SMulCommClass S R N]

/-- Scalar commutators are additive in the linear map. -/
theorem scalarCommutator_add (D E : M →ₗ[R] N) (g : S) :
    (D + E).scalarCommutator g = D.scalarCommutator g + E.scalarCommutator g := by
  apply LinearMap.ext
  intro m
  simp only [scalarCommutator_apply, add_apply, smul_add, add_sub_add_comm]

/-- The scalar commutator of a composite splits into the two lower-order commutators. -/
theorem scalarCommutator_comp (D : L →ₗ[R] M) (D' : M →ₗ[R] N) (g : S) :
    (D'.comp D).scalarCommutator g =
      D'.comp (D.scalarCommutator g) + (D'.scalarCommutator g).comp D := by
  apply LinearMap.ext
  intro m
  simp only [scalarCommutator_apply, comp_apply, add_apply, map_sub]
  exact (sub_add_sub_cancel _ _ _).symm

namespace IsDifferentialOperatorOfOrder

/-- The zero map has every differential-operator order bound. -/
theorem zero (k : ℕ) :
    (0 : M →ₗ[R] N).IsDifferentialOperatorOfOrder S k := by
  induction k with
  | zero =>
      intro g
      simp [scalarCommutator]
  | succ k ih =>
      intro g
      simpa [scalarCommutator] using ih

/-- The sum of two operators of the same order bound has that order bound. -/
theorem add {k : ℕ} {D E : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrder S k)
    (hE : E.IsDifferentialOperatorOfOrder S k) :
    (D + E).IsDifferentialOperatorOfOrder S k := by
  induction k generalizing D E with
  | zero =>
      intro g
      rw [scalarCommutator_add, hD g, hE g, add_zero]
  | succ k ih =>
      intro g
      rw [scalarCommutator_add]
      exact ih (hD g) (hE g)

/-- Negating an operator preserves its differential-operator order bound. -/
theorem neg {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    (-D).IsDifferentialOperatorOfOrder S k := by
  have hneg (E : M →ₗ[R] N) (g : S) :
      (-E).scalarCommutator g = -(E.scalarCommutator g) := by
    apply LinearMap.ext
    intro m
    simp [sub_eq_add_neg, add_comm]
  induction k generalizing D with
  | zero =>
      intro g
      rw [hneg, hD g, neg_zero]
  | succ k ih =>
      intro g
      rw [hneg]
      exact ih (hD g)

/-- The identity endomorphism has differential-operator order zero. -/
theorem id :
    (LinearMap.id : M →ₗ[R] M).IsDifferentialOperatorOfOrder S 0 := by
  intro g
  apply LinearMap.ext
  intro m
  simp

/-- Composing two differential operators adds their order bounds. -/
theorem comp {k k' : ℕ} {D : L →ₗ[R] M} {D' : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrder S k)
    (hD' : D'.IsDifferentialOperatorOfOrder S k') :
    (D'.comp D).IsDifferentialOperatorOfOrder S (k + k') := by
  induction k generalizing k' D D' with
  | zero =>
      induction k' generalizing D' with
      | zero =>
          intro g
          rw [scalarCommutator_comp, hD g, hD' g, comp_zero, zero_comp, add_zero]
      | succ k' ih =>
          rw [Nat.zero_add, isDifferentialOperatorOfOrder_succ_iff]
          intro g
          rw [scalarCommutator_comp, hD g, comp_zero, zero_add]
          simpa only [Nat.zero_add] using ih (hD' g)
  | succ k ih =>
      induction k' generalizing D' with
      | zero =>
          rw [Nat.add_zero, isDifferentialOperatorOfOrder_succ_iff]
          intro g
          rw [scalarCommutator_comp, hD' g, zero_comp, add_zero]
          simpa only [Nat.add_zero] using ih (hD g) hD'
      | succ k' ih' =>
          rw [Nat.add_succ, isDifferentialOperatorOfOrder_succ_iff]
          intro g
          rw [scalarCommutator_comp]
          apply add
          · simpa only [Nat.succ_add, Nat.add_succ] using ih (hD g) hD'
          · exact ih' (hD' g)

/-- An operator with order bound `k` has the successor order bound `k + 1`. -/
theorem le_succ {D : M →ₗ[R] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    D.IsDifferentialOperatorOfOrder S (k + 1) := by
  induction k generalizing D with
  | zero =>
      intro g
      rw [hD g]
      exact zero 0
  | succ k ih =>
      intro g
      exact ih (hD g)

/-- An operator with order bound `k` has every larger order bound. -/
theorem mono {D : M →ₗ[R] N} {k l : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) (hkl : k ≤ l) :
    D.IsDifferentialOperatorOfOrder S l := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction n with
  | zero => simpa using hD
  | succ n ih => exact ih.le_succ

end IsDifferentialOperatorOfOrder

end OrderClosure

section ScalarClosure

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w'}
variable [Semiring R] [Semiring S]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [DistribSMul S M] [Module S N]
variable [SMulCommClass S R M] [SMulCommClass S R N] [SMulCommClass R S N]
variable [SMulCommClass S S N]

/-- Scalar multiplication on the target commutes with scalar commutators. -/
theorem scalarCommutator_smul (c g : S) (D : M →ₗ[R] N) :
    (c • D).scalarCommutator g = c • D.scalarCommutator g := by
  apply LinearMap.ext
  intro m
  change c • D (g • m) - g • (c • D m) = c • (D (g • m) - g • D m)
  rw [smul_sub, smul_comm g c]

namespace IsDifferentialOperatorOfOrder

/-- Scaling an operator of order at most `k` by an output scalar preserves its order bound. -/
theorem smul {k : ℕ} {D : M →ₗ[R] N} (c : S)
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    (c • D).IsDifferentialOperatorOfOrder S k := by
  induction k generalizing D with
  | zero =>
      intro g
      rw [scalarCommutator_smul, hD g, smul_zero]
  | succ k ih =>
      intro g
      rw [scalarCommutator_smul]
      exact ih (hD g)

end IsDifferentialOperatorOfOrder

end ScalarClosure

section ScalarEndomorphism

variable {R : Type u} {S : Type v} {M : Type w}
variable [Semiring R] [AddCommGroup M] [Module R M]
variable [DistribSMul S M] [SMulCommClass S R M] [SMulCommClass S S M]

/-- Multiplication by a scalar is a differential operator of order zero. -/
theorem isDifferentialOperatorOfOrder_smul (s : S) :
    (DistribSMul.toLinearMap R M s : Module.End R M).IsDifferentialOperatorOfOrder S 0 := by
  rw [isDifferentialOperatorOfOrder_zero_iff]
  intro g m
  exact smul_comm s g m

end ScalarEndomorphism

end LinearMap

section OperatorSubmodule

open LinearMap

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w'}
variable [Semiring R] [Semiring S]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [DistribSMul S M] [Module S N]
variable [SMulCommClass S R M] [SMulCommClass S R N] [SMulCommClass R S N]
variable [SMulCommClass S S N]

/-- The `S`-submodule of `R`-linear differential operators `M → N` of order at most `k`. -/
@[stacks 09CI]
def differentialOperatorsOrderLESubmodule (R : Type u) (S : Type v) (M : Type w)
    [Semiring R] [Semiring S]
    [AddCommGroup M] [Module R M] [DistribSMul S M] [SMulCommClass S R M]
    (k : ℕ) (N : Type w')
    [AddCommGroup N] [Module R N] [Module S N]
    [SMulCommClass S R N] [SMulCommClass R S N] [SMulCommClass S S N] :
    Submodule S (M →ₗ[R] N) where
  carrier := { D | D.IsDifferentialOperatorOfOrder S k }
  zero_mem' := IsDifferentialOperatorOfOrder.zero k
  add_mem' := fun hD hE => hD.add hE
  smul_mem' := fun c _ hD => hD.smul c

/-- Membership in the order-bounded differential-operator submodule is the recursive order
predicate. -/
@[simp]
theorem mem_differentialOperatorsOrderLESubmodule_iff {D : M →ₗ[R] N} {k : ℕ} :
    D ∈ differentialOperatorsOrderLESubmodule R S M k N ↔
      D.IsDifferentialOperatorOfOrder S k := Iff.rfl

/-- The type of `R`-linear differential operators `M → N` of order at most `k`. -/
@[stacks 09CI]
abbrev differentialOperatorsOrderLE (R : Type u) (S : Type v) (M : Type w)
    [Semiring R] [Semiring S]
    [AddCommGroup M] [Module R M] [DistribSMul S M] [SMulCommClass S R M]
    (k : ℕ) (N : Type w')
    [AddCommGroup N] [Module R N] [Module S N]
    [SMulCommClass S R N] [SMulCommClass R S N] [SMulCommClass S S N] :=
  differentialOperatorsOrderLESubmodule R S M k N

namespace differentialOperatorsOrderLE

/-- Regard an operator with order bound `k` as one with a larger order bound `l`. -/
def castLE {k l : ℕ} (hkl : k ≤ l) (D : differentialOperatorsOrderLE R S M k N) :
    differentialOperatorsOrderLE R S M l N :=
  ⟨D, D.2.mono hkl⟩

/-- Coercing an order-widened differential operator recovers the original linear map. -/
@[simp]
theorem coe_castLE {k l : ℕ} (hkl : k ≤ l) (D : differentialOperatorsOrderLE R S M k N) :
    ((castLE hkl D : differentialOperatorsOrderLE R S M l N) : M →ₗ[R] N) = D := rfl

end differentialOperatorsOrderLE

end OperatorSubmodule

section BoundedComposition

open LinearMap

variable {R : Type u} {S : Type v} {M₁ : Type w} {M₂ : Type w'} {M₃ : Type*}
variable [Semiring R] [Semiring S]
variable [AddCommGroup M₁] [Module R M₁] [DistribSMul S M₁] [SMulCommClass S R M₁]
variable [AddCommGroup M₂] [Module R M₂] [Module S M₂]
variable [SMulCommClass S R M₂] [SMulCommClass R S M₂] [SMulCommClass S S M₂]
variable [AddCommGroup M₃] [Module R M₃] [Module S M₃]
variable [SMulCommClass S R M₃] [SMulCommClass R S M₃] [SMulCommClass S S M₃]

namespace differentialOperatorsOrderLE

/-- Composition of order-bounded differential operators has the sum of the two order bounds. -/
@[stacks 09CJ]
def comp {k₁ k₂ : ℕ} (D₂ : differentialOperatorsOrderLE R S M₂ k₂ M₃)
    (D₁ : differentialOperatorsOrderLE R S M₁ k₁ M₂) :
    differentialOperatorsOrderLE R S M₁ (k₁ + k₂) M₃ :=
  ⟨(D₂ : M₂ →ₗ[R] M₃).comp (D₁ : M₁ →ₗ[R] M₂),
    D₁.2.comp D₂.2⟩

/-- Coercing the composition of order-bounded operators recovers ordinary composition. -/
@[simp]
theorem coe_comp {k₁ k₂ : ℕ} (D₂ : differentialOperatorsOrderLE R S M₂ k₂ M₃)
    (D₁ : differentialOperatorsOrderLE R S M₁ k₁ M₂) :
    ((comp D₂ D₁ : differentialOperatorsOrderLE R S M₁ (k₁ + k₂) M₃) : M₁ →ₗ[R] M₃) =
      (D₂ : M₂ →ₗ[R] M₃).comp (D₁ : M₁ →ₗ[R] M₂) := rfl

end differentialOperatorsOrderLE

end BoundedComposition

section BoundedFunctoriality

open LinearMap

variable {R : Type u} {S : Type v} {M₁ : Type w} {M₂ : Type w'} {M₃ : Type*}
variable [Semiring R] [Semiring S]
variable [AddCommGroup M₁] [Module R M₁] [DistribSMul S M₁] [SMulCommClass S R M₁]
variable [AddCommGroup M₂] [Module R M₂] [Module S M₂]
variable [SMulCommClass S R M₂] [SMulCommClass R S M₂] [SMulCommClass S S M₂]
variable [AddCommGroup M₃] [Module R M₃] [Module S M₃]
variable [SMulCommClass S R M₃] [SMulCommClass R S M₃] [SMulCommClass S S M₃]

namespace differentialOperatorsOrderLE

/-- Postcomposition by an `S`-linear map preserves a fixed differential-operator order bound.
The explicit `CompatibleSMul` input is the exact condition needed to view the `S`-linear map as
an `R`-linear map; no algebra-tower presentation is part of this API. -/
@[stacks 09CK]
def postcompose [LinearMap.CompatibleSMul M₂ M₃ R S] (f : M₂ →ₗ[S] M₃) {k : ℕ} :
    differentialOperatorsOrderLE R S M₁ k M₂ →ₗ[S]
      differentialOperatorsOrderLE R S M₁ k M₃ where
  toFun D := ⟨(f.restrictScalars R).comp (D : M₁ →ₗ[R] M₂), by
    change ((f.restrictScalars R).comp (D : M₁ →ₗ[R] M₂)).IsDifferentialOperatorOfOrder S k
    have hf : (f.restrictScalars R).IsDifferentialOperatorOfOrder S 0 :=
      (isDifferentialOperatorOfOrder_zero_iff _).2 (fun g m => f.map_smul g m)
    simpa only [Nat.add_zero] using D.2.comp hf⟩
  map_add' := by
    intro D E
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    exact f.map_add (D.1 m) (E.1 m)
  map_smul' := by
    intro c D
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    exact f.map_smul c (D.1 m)

/-- Coercing `postcompose f D` gives ordinary composition with `f`. -/
@[simp]
theorem coe_postcompose [LinearMap.CompatibleSMul M₂ M₃ R S] (f : M₂ →ₗ[S] M₃)
    {k : ℕ} (D : differentialOperatorsOrderLE R S M₁ k M₂) :
    ((postcompose (R := R) (S := S) (M₁ := M₁) f D :
      differentialOperatorsOrderLE R S M₁ k M₃) : M₁ →ₗ[R] M₃) =
      (f.restrictScalars R).comp (D : M₁ →ₗ[R] M₂) := rfl

end differentialOperatorsOrderLE

end BoundedFunctoriality

section BoundedContravariantFunctoriality

open LinearMap

variable {R : Type u} {S : Type v} {M₁ : Type w} {M₂ : Type w'} {M₃ : Type*}
variable [Semiring R] [Semiring S]
variable [AddCommGroup M₁] [Module R M₁] [Module S M₁] [SMulCommClass S R M₁]
variable [AddCommGroup M₂] [Module R M₂] [Module S M₂] [SMulCommClass S R M₂]
variable [AddCommGroup M₃] [Module R M₃] [Module S M₃]
variable [SMulCommClass S R M₃] [SMulCommClass R S M₃] [SMulCommClass S S M₃]

namespace differentialOperatorsOrderLE

/-- Precomposition by an `S`-linear map preserves a fixed differential-operator order bound.
As for `postcompose`, `CompatibleSMul` records exactly the scalar compatibility needed to
restrict the input map to an `R`-linear map. -/
@[stacks 09CK]
def precompose [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ →ₗ[S] M₂) {k : ℕ} :
    differentialOperatorsOrderLE R S M₂ k M₃ →ₗ[S]
      differentialOperatorsOrderLE R S M₁ k M₃ where
  toFun D := ⟨(D : M₂ →ₗ[R] M₃).comp (f.restrictScalars R), by
    change ((D : M₂ →ₗ[R] M₃).comp (f.restrictScalars R)).IsDifferentialOperatorOfOrder S k
    have hf : (f.restrictScalars R).IsDifferentialOperatorOfOrder S 0 :=
      (isDifferentialOperatorOfOrder_zero_iff _).2 (fun g m => f.map_smul g m)
    simpa only [Nat.zero_add] using hf.comp D.2⟩
  map_add' := by
    intro D E
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c D
    apply Subtype.ext
    rfl

/-- Coercing `precompose f D` gives ordinary composition with `f`. -/
@[simp]
theorem coe_precompose [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ →ₗ[S] M₂)
    {k : ℕ} (D : differentialOperatorsOrderLE R S M₂ k M₃) :
    ((precompose (R := R) (S := S) (M₃ := M₃) f D :
      differentialOperatorsOrderLE R S M₁ k M₃) : M₁ →ₗ[R] M₃) =
      (D : M₂ →ₗ[R] M₃).comp (f.restrictScalars R) := rfl

end differentialOperatorsOrderLE

end BoundedContravariantFunctoriality

section BoundedBifunctoriality

open LinearMap

variable {R : Type u} {S : Type v}
variable {M₀ : Type*} {M₁ : Type w} {M₂ : Type w'} {M₃ : Type*} {M₄ : Type*} {M₅ : Type*}
variable [Semiring R] [Semiring S]
variable [AddCommGroup M₀] [Module R M₀] [Module S M₀] [SMulCommClass S R M₀]
variable [AddCommGroup M₁] [Module R M₁] [Module S M₁] [SMulCommClass S R M₁]
variable [AddCommGroup M₂] [Module R M₂] [Module S M₂] [SMulCommClass S R M₂]
variable [AddCommGroup M₃] [Module R M₃] [Module S M₃]
variable [SMulCommClass S R M₃] [SMulCommClass R S M₃] [SMulCommClass S S M₃]
variable [AddCommGroup M₄] [Module R M₄] [Module S M₄]
variable [SMulCommClass S R M₄] [SMulCommClass R S M₄] [SMulCommClass S S M₄]
variable [AddCommGroup M₅] [Module R M₅] [Module S M₅]
variable [SMulCommClass S R M₅] [SMulCommClass R S M₅] [SMulCommClass S S M₅]

namespace differentialOperatorsOrderLE

/-- Simultaneously precompose and postcompose an order-bounded differential operator.

The source map is contravariant and the target map is covariant.  The two
`CompatibleSMul` hypotheses are exactly the data needed to restrict the two
`S`-linear maps to `R`-linear maps. -/
@[stacks 09CI "two-sided functoriality of differential operators"]
def bimap [CompatibleSMul M₁ M₂ R S] [CompatibleSMul M₃ M₄ R S]
    (g : M₁ →ₗ[S] M₂) (h : M₃ →ₗ[S] M₄) {k : ℕ} :
    differentialOperatorsOrderLE R S M₂ k M₃ →ₗ[S]
      differentialOperatorsOrderLE R S M₁ k M₄ :=
  (postcompose (R := R) (S := S) (M₁ := M₁) h).comp
    (precompose (R := R) (S := S) (M₃ := M₃) g)

/-- Coercing `bimap g h D` gives ordinary composition on both sides. -/
@[simp]
theorem coe_bimap [CompatibleSMul M₁ M₂ R S] [CompatibleSMul M₃ M₄ R S]
    (g : M₁ →ₗ[S] M₂) (h : M₃ →ₗ[S] M₄)
    {k : ℕ} (D : differentialOperatorsOrderLE R S M₂ k M₃) :
    ((bimap (R := R) (S := S) g h D :
      differentialOperatorsOrderLE R S M₁ k M₄) : M₁ →ₗ[R] M₄) =
      (h.restrictScalars R).comp
        ((D : M₂ →ₗ[R] M₃).comp (g.restrictScalars R)) := rfl

/-- Acting by identities in both variables leaves an order-bounded operator unchanged. -/
@[simp]
theorem bimap_id [CompatibleSMul M₁ M₁ R S] [CompatibleSMul M₃ M₃ R S] {k : ℕ} :
    bimap (R := R) (S := S)
        (LinearMap.id : M₁ →ₗ[S] M₁) (LinearMap.id : M₃ →ₗ[S] M₃) =
      (LinearMap.id : differentialOperatorsOrderLE R S M₁ k M₃ →ₗ[S]
        differentialOperatorsOrderLE R S M₁ k M₃) := by
  apply LinearMap.ext
  intro D
  apply Subtype.ext
  apply LinearMap.ext
  intro m
  rfl

/-- Two-sided actions compose contravariantly in the source and covariantly in the target. -/
@[simp]
theorem bimap_comp [CompatibleSMul M₀ M₁ R S] [CompatibleSMul M₁ M₂ R S]
    [CompatibleSMul M₀ M₂ R S] [CompatibleSMul M₃ M₄ R S] [CompatibleSMul M₄ M₅ R S]
    [CompatibleSMul M₃ M₅ R S]
    (g₁ : M₁ →ₗ[S] M₂) (g₂ : M₀ →ₗ[S] M₁)
    (h₁ : M₃ →ₗ[S] M₄) (h₂ : M₄ →ₗ[S] M₅) {k : ℕ} :
    (bimap (R := R) (S := S) (M₁ := M₀) (M₂ := M₁) (M₃ := M₄) (M₄ := M₅)
      (k := k) g₂ h₂).comp
          (bimap (R := R) (S := S) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) (M₄ := M₄)
            (k := k) g₁ h₁) =
      bimap (R := R) (S := S) (M₁ := M₀) (M₂ := M₂) (M₃ := M₃) (M₄ := M₅) (k := k)
        (g₁ ∘ₗ g₂ : M₀ →ₗ[S] M₂) (h₂ ∘ₗ h₁ : M₃ →ₗ[S] M₅) := by
  apply LinearMap.ext
  intro D
  apply Subtype.ext
  apply LinearMap.ext
  intro m
  rfl

end differentialOperatorsOrderLE

end BoundedBifunctoriality
