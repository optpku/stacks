/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Group.Action.NatInt

/-!
# Extending an internal natural grading to the integers

An internally `ℕ`-graded module has a canonical `ℤ`-indexed presentation obtained by putting the
negative pieces equal to `⊥`.  This leaf is about submodule families on one module; the separate
`DirectSum.natToIntGrading` leaf handles direct-sum carriers.
-/

@[expose] public section

noncomputable section

universe uR uM

namespace DirectSum.Decomposition

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- Extend an internal `ℕ`-grading by zero to an internal `ℤ`-grading. -/
@[reducible, stacks 00K8 "internal natural grading extended to integers", stacks 00K3]
def natToIntGrading
    (𝒩 : ℕ → Submodule R M) (d : ℤ) : Submodule R M :=
  if 0 ≤ d then 𝒩 d.toNat else ⊥

/-- The nonnegative branch of `natToIntGrading`. -/
@[simp, stacks 00K8 "nonnegative branch of integer grading", stacks 00K3]
theorem natToIntGrading_eq_nat {𝒩 : ℕ → Submodule R M} {d : ℤ} (hd : 0 ≤ d) :
    natToIntGrading 𝒩 d = 𝒩 d.toNat := sorry

/-- The negative branch of `natToIntGrading`. -/
@[simp, stacks 00K8 "negative branch of integer grading", stacks 00K3]
theorem natToIntGrading_eq_bot {𝒩 : ℕ → Submodule R M} {d : ℤ} (hd : d < 0) :
    natToIntGrading 𝒩 d = ⊥ := sorry

/-- The natural degree `n` is represented by the original degree-`n` piece. -/
@[simp, stacks 00K8 "natural degree in integer grading", stacks 00K3]
theorem natToIntGrading_nat_eq (𝒩 : ℕ → Submodule R M) (n : ℕ) :
    natToIntGrading 𝒩 (n : ℤ) = 𝒩 n := sorry

/-- The original component and its integer extension are linearly equivalent. -/
@[stacks 00K8 "natural component equivalence in integer grading", stacks 00K3]
def natToIntGradingEquiv
    (𝒩 : ℕ → Submodule R M) (n : ℕ) :
    𝒩 n ≃ₗ[R] natToIntGrading 𝒩 (n : ℤ) :=
  LinearEquiv.ofEq _ _ rfl

/-- The component equivalence does not change the ambient module element. -/
@[simp, stacks 00K8 "integer grading component coercion", stacks 00K3]
theorem natToIntGradingEquiv_coe
    (𝒩 : ℕ → Submodule R M) (n : ℕ) (x : 𝒩 n) :
    ((natToIntGradingEquiv 𝒩 n x : natToIntGrading 𝒩 (n : ℤ)) : M) = (x : M) := sorry

/-- The map from a natural homogeneous component into its matching integer direct-sum slot.

This named linear map keeps the reindexing data visible to downstream constructions instead of
making it an opaque component of a chosen decomposition instance. -/
@[stacks 00K8 "natural-to-integer component inclusion", stacks 00K3]
noncomputable def natToIntComponentMap
    (𝒩 : ℕ → Submodule R M) (n : ℕ) :
    𝒩 n →ₗ[R] DirectSum ℤ (fun d ↦ natToIntGrading 𝒩 d) :=
  (DirectSum.lof R ℤ (fun d ↦ natToIntGrading 𝒩 d) (n : ℤ)).comp
    (natToIntGradingEquiv 𝒩 n).toLinearMap

/-- Lift all natural homogeneous components into their matching integer slots using the canonical
linear universal property of `DirectSum`. -/
@[stacks 00K8 "natural-to-integer direct-sum lift", stacks 00K3]
noncomputable def natToIntLift
    (𝒩 : ℕ → Submodule R M) :
    DirectSum ℕ (fun n ↦ 𝒩 n) →ₗ[R]
      DirectSum ℤ (fun d ↦ natToIntGrading 𝒩 d) :=
  DirectSum.toModule R ℕ
    (DirectSum ℤ (fun d ↦ natToIntGrading 𝒩 d))
    (natToIntComponentMap 𝒩)

/-- The direct-sum lift is computed on a natural summand by the named component map. -/
@[simp, stacks 00K8 "natural-to-integer lift on a summand", stacks 00K3]
theorem natToIntLift_lof
    (𝒩 : ℕ → Submodule R M) (n : ℕ) (x : 𝒩 n) :
    natToIntLift 𝒩 (DirectSum.lof R ℕ (fun n ↦ 𝒩 n) n x) =
      natToIntComponentMap 𝒩 n x := sorry

/-- The decomposition map for the integer extension. -/
@[stacks 00K8 "integer extension decomposition map", stacks 00K3]
noncomputable def natToIntDecompose
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩] :
    M →ₗ[R] DirectSum ℤ (fun d ↦ natToIntGrading 𝒩 d) :=
  (natToIntLift 𝒩).comp (DirectSum.decomposeLinearEquiv 𝒩).toLinearMap

/-- Recomposing the explicit integer decomposition recovers the original module element. -/
@[stacks 00K8 "integer extension decomposition left inverse", stacks 00K3]
theorem natToIntDecompose_left_inv
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩] :
    DirectSum.coeLinearMap (natToIntGrading 𝒩) ∘ₗ natToIntDecompose 𝒩 =
      LinearMap.id := sorry

/-- Decomposing after recomposition is the identity on the integer direct sum. -/
@[stacks 00K8 "integer extension decomposition right inverse", stacks 00K3]
theorem natToIntDecompose_right_inv
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩] :
    natToIntDecompose 𝒩 ∘ₗ DirectSum.coeLinearMap (natToIntGrading 𝒩) =
      LinearMap.id := sorry

/-- The integer extension is internally decomposed whenever the original family is.

The direct-sum map is explicit in `natToIntDecompose`; only the two inverse laws are deferred.
This is important because `DirectSum.Decomposition` is a data-bearing class, not merely a
proposition. -/
@[reducible, instance 100, stacks 00K8 "integer extension internal decomposition", stacks 00K3]
noncomputable instance natToIntGradingDecomposition
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩] :
    DirectSum.Decomposition (natToIntGrading 𝒩) :=
  DirectSum.Decomposition.ofLinearMap
    (natToIntGrading 𝒩) (natToIntDecompose 𝒩)
    (natToIntDecompose_left_inv 𝒩) (natToIntDecompose_right_inv 𝒩)

/-- The nonnegative integer component of the extended decomposition agrees with the natural one. -/
@[simp, stacks 00K8 "integer extension decomposition on natural degree", stacks 00K3]
theorem natToIntDecompose_nat_apply
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩]
    (x : M) (n : ℕ) :
    ((natToIntDecompose 𝒩 x (n : ℤ) : natToIntGrading 𝒩 (n : ℤ)) : M) =
      ((DirectSum.decompose 𝒩 x n : 𝒩 n) : M) := sorry

/-- The integer decomposition coordinate is the natural coordinate transported by the component
equivalence.  This subtype-level form is the rewrite-friendly companion of
`natToIntDecompose_nat_apply`. -/
@[stacks 00K8 "integer decomposition natural coordinate", stacks 00K3]
theorem natToIntDecompose_component
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩]
    (x : M) (n : ℕ) :
    DirectSum.component R ℤ (fun d ↦ natToIntGrading 𝒩 d) (n : ℤ)
        (natToIntDecompose 𝒩 x) =
      natToIntGradingEquiv 𝒩 n (DirectSum.decompose 𝒩 x n) := sorry

/-- A natural homogeneous element is recovered in its matching integer coordinate. -/
@[simp, stacks 00K8 "integer decomposition matching natural coordinate", stacks 00K3]
theorem natToIntDecompose_component_coe
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩]
    (n : ℕ) (x : 𝒩 n) :
    DirectSum.component R ℤ (fun d ↦ natToIntGrading 𝒩 d) (n : ℤ)
        (natToIntDecompose 𝒩 (x : M)) = natToIntGradingEquiv 𝒩 n x := sorry

/-- A natural homogeneous element has zero coordinate in every different natural degree after
extension to the integer grading. -/
@[simp, stacks 00K8 "integer decomposition off-diagonal natural coordinate", stacks 00K3]
theorem natToIntDecompose_component_ne
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩]
    {i m : ℕ} (him : i ≠ m) (x : 𝒩 i) :
    DirectSum.component R ℤ (fun d ↦ natToIntGrading 𝒩 d) (m : ℤ)
        (natToIntDecompose 𝒩 (x : M)) = 0 := sorry

/-- Negative components of the extended decomposition have zero ambient value. -/
@[simp, stacks 00K8 "integer extension decomposition on negative degree", stacks 00K3]
theorem natToIntDecompose_neg_apply
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩]
    (x : M) {d : ℤ} (hd : d < 0) :
    ((natToIntDecompose 𝒩 x d : natToIntGrading 𝒩 d) : M) = 0 := sorry

/-- Negative integer coordinates of the explicit decomposition are the zero element of the
corresponding bottom component. -/
@[simp, stacks 00K8 "integer decomposition negative coordinate", stacks 00K3]
theorem natToIntDecompose_component_neg
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩]
    (x : M) {d : ℤ} (hd : d < 0) :
    DirectSum.component R ℤ (fun e ↦ natToIntGrading 𝒩 e) d
        (natToIntDecompose 𝒩 x) = 0 := sorry

/-- The canonical `DirectSum.decompose` for the extended family is the named explicit map. -/
@[simp, stacks 00K8 "integer extension named decomposition", stacks 00K3]
theorem decompose_natToInt
    (𝒩 : ℕ → Submodule R M) [DirectSum.Decomposition 𝒩] (x : M) :
    DirectSum.decompose (natToIntGrading 𝒩) x = natToIntDecompose 𝒩 x := sorry

universe uA uσ

variable {A : Type uA} {σ : Type uσ} [SetLike σ A]
variable [SMulZeroClass A M]

/-- A graded scalar action extends across the natural-to-integer module grading. -/
@[instance 100, stacks 00K8 "graded scalar action on integer extension", stacks 00K3]
theorem natToIntGrading_gradedSMul
    (𝒜 : ℕ → σ) (𝒩 : ℕ → Submodule R M)
    [SetLike.GradedSMul 𝒜 𝒩] :
    SetLike.GradedSMul 𝒜 (fun d : ℤ ↦ natToIntGrading 𝒩 d) := sorry

end DirectSum.Decomposition

end
