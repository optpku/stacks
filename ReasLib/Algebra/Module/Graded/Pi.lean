/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coordinatewise gradings on dependent products

This leaf owns the neutral additive and linear-algebraic construction obtained by taking a
dependent product of internally graded modules.  The coordinate family is dependent: the `k`th
factor may have a different carrier and a different family of homogeneous submodules.  When the
coordinate type is finite, the product grading has the canonical direct-sum decomposition exposed
below.  Algebra, quotient, and source-specific degree data belong in leaves which import this one.
-/

@[expose] public section

open scoped BigOperators DirectSum

noncomputable section

universe u v w x y z a

namespace GradedModule
namespace Pi

variable {R : Type u} [Semiring R]
variable {ι : Type v}
variable {κ : Type w}
variable {M : κ → Type x}
variable [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)]

/-- The coordinatewise `d`th homogeneous submodule of a dependent product. -/
@[stacks 052N "coordinatewise product grading"]
def grading (ℳ : ∀ k, ι → Submodule R (M k)) (d : ι) :
    Submodule R (∀ k, M k) :=
  Submodule.pi Set.univ (fun k ↦ ℳ k d)

/-- Membership in a coordinatewise product grading is coordinatewise membership. -/
@[simp, stacks 052N "coordinatewise product grading membership"]
theorem mem_grading_iff
    (ℳ : ∀ k, ι → Submodule R (M k)) (d : ι) {v : ∀ k, M k} :
    v ∈ grading ℳ d ↔ ∀ k, v k ∈ ℳ k d := sorry

section Single

variable [DecidableEq κ]

/-- A homogeneous element in one factor gives a homogeneous element of the product. -/
@[stacks 052N "single-coordinate homogeneous membership"]
theorem single_mem
    (ℳ : ∀ k, ι → Submodule R (M k)) (k : κ) (d : ι) {x : ℳ k d} :
    (LinearMap.single R M k) x ∈ grading ℳ d := sorry

/-- The canonical linear inclusion of the `k`th homogeneous factor into the product piece. -/
@[stacks 052N "single-coordinate homogeneous inclusion"]
def single
    (ℳ : ∀ k, ι → Submodule R (M k)) (k : κ) (d : ι) :
    ℳ k d →ₗ[R] grading ℳ d :=
  LinearMap.codRestrict
    (grading ℳ d)
    ((LinearMap.single R M k).comp (ℳ k d).subtype)
    (fun x ↦ single_mem (R := R) (M := M) ℳ k d (x := x))

/-- The underlying product-valued map of `single` is Mathlib's dependent `LinearMap.single`. -/
@[simp, stacks 052N "single-coordinate inclusion coercion"]
theorem single_coe
    (ℳ : ∀ k, ι → Submodule R (M k)) (k : κ) (d : ι) (x : ℳ k d) :
    ((single ℳ k d x : grading ℳ d) : ∀ j, M j) =
      (LinearMap.single R M k) x := sorry

/-- Evaluation of `single` at a coordinate agrees with dependent `Pi.single`. -/
@[simp, stacks 052N "single-coordinate inclusion evaluation"]
theorem single_apply
    (ℳ : ∀ k, ι → Submodule R (M k)) (k : κ) (d : ι) (x : ℳ k d) (j : κ) :
    ((single ℳ k d x : grading ℳ d) : ∀ j, M j) j =
      (_root_.Pi.single k (x : M k)) j := sorry

end Single

section GradedAction

variable {ιA : Type a} [VAdd ιA ι]
variable {A : Type y} {σ : Type z} [SetLike σ A]
variable [∀ k, SMul A (M k)]

/-- A homogeneous scalar and a homogeneous product vector multiply into the degree `i +ᵥ j` piece.

The scalar and module grading indices may differ; `VAdd ιA ι` supplies their degree action.  The
action on the dependent product is the canonical pointwise `SMul` induced by the coordinate
actions; the base ring `R` of the submodules is independent of the scalar type `A`. -/
@[stacks 052N "coordinatewise graded scalar membership"]
theorem smul_mem_grading
    (𝒜 : ιA → σ) (ℳ : ∀ k, ι → Submodule R (M k))
    [∀ k, SetLike.GradedSMul 𝒜 (ℳ k)]
    {i : ιA} {j : ι} {a : A} {v : ∀ k, M k}
    (ha : a ∈ 𝒜 i) (hv : v ∈ grading ℳ j) :
    a • v ∈ grading ℳ (i +ᵥ j) := sorry

/-- Coordinatewise homogeneous scalar multiplication on a product grading. -/
@[stacks 052N "coordinatewise graded scalar action"]
theorem gradedSMul
    (𝒜 : ιA → σ) (ℳ : ∀ k, ι → Submodule R (M k))
    [∀ k, SetLike.GradedSMul 𝒜 (ℳ k)] :
    SetLike.GradedSMul 𝒜 (grading ℳ) := sorry

/-- Install the canonical coordinatewise graded scalar action as the reusable instance. -/
@[stacks 052N "coordinatewise graded scalar action instance"]
instance (priority := 100) instGradedSMul
    (𝒜 : ιA → σ) (ℳ : ∀ k, ι → Submodule R (M k))
    [∀ k, SetLike.GradedSMul 𝒜 (ℳ k)] :
    SetLike.GradedSMul 𝒜 (grading ℳ) :=
  gradedSMul 𝒜 ℳ

end GradedAction

section Decomposition

variable [DecidableEq ι] [DecidableEq κ]
variable (ℳ : ∀ k, ι → Submodule R (M k))
variable [∀ k, DirectSum.Decomposition (ℳ k)]

/-- Recompose the decomposition of one factor after inserting it in one product coordinate. -/
@[stacks 052N "single-coordinate graded recomposition"]
theorem coordinate_recompose
    (k : κ) :
    (DirectSum.coeLinearMap (fun d ↦ grading ℳ d)).comp
        ((DirectSum.lmap (fun d ↦ single ℳ k d)).comp
          (DirectSum.decomposeLinearEquiv (ℳ k)).toLinearMap) =
      LinearMap.single R M k := sorry

variable [Fintype κ]

/-- Decompose every coordinate and place its homogeneous pieces in the corresponding product
component. -/
@[stacks 052N "coordinatewise graded predecomposition"]
noncomputable def predecompose :
    (∀ k, M k) →ₗ[R] DirectSum ι (fun d ↦ grading ℳ d) :=
  ∑ k : κ,
    (DirectSum.lmap (fun d ↦ single ℳ k d)).comp
      ((DirectSum.decomposeLinearEquiv (ℳ k)).toLinearMap.comp
        (LinearMap.proj k))

/-- The `d`th component of `predecompose` is obtained by decomposing every input coordinate in
degree `d`. -/
@[stacks 052N "coordinatewise graded component formula"]
theorem predecompose_component
    (v : ∀ k, M k) (d : ι) :
    ((predecompose ℳ v d : grading ℳ d) : ∀ k, M k) =
      fun k ↦
        ((DirectSum.decompose (ℳ k) (v k) d : ℳ k d) : M k) := sorry

/-- The coordinatewise predecomposition recomposes to the original product vector. -/
@[stacks 052N "coordinatewise graded decomposition left inverse"]
theorem predecompose_left_inv :
    (DirectSum.coeLinearMap (fun d ↦ grading ℳ d)).comp (predecompose ℳ) =
      LinearMap.id := sorry

/-- The coordinatewise predecomposition is inverse to recomposition from the graded direct sum. -/
@[stacks 052N "coordinatewise graded decomposition right inverse"]
theorem predecompose_right_inv :
    (predecompose ℳ).comp (DirectSum.coeLinearMap (fun d ↦ grading ℳ d)) =
      LinearMap.id := sorry

/-- A homogeneous product vector is sent by `predecompose` to its matching direct-sum summand. -/
@[stacks 052N "coordinatewise homogeneous direct-sum summand"]
theorem predecompose_eq_lof_of_mem
    {v : ∀ k, M k} {d : ι}
    (hv : v ∈ grading ℳ d) :
    predecompose ℳ v =
      DirectSum.lof R ι (fun e ↦ grading ℳ e) d ⟨v, hv⟩ := sorry

/-- The product grading carries the canonical internal direct-sum decomposition induced by the
coordinate decompositions. -/
@[reducible, stacks 052N "coordinatewise graded decomposition"]
noncomputable def decomposition :
    DirectSum.Decomposition (grading ℳ) :=
  DirectSum.Decomposition.ofLinearMap
    (ℳ := grading ℳ)
    (predecompose ℳ)
    (predecompose_left_inv ℳ)
    (predecompose_right_inv ℳ)

/-- Install the canonical product decomposition when every coordinate is decomposed and the
coordinate type is finite. -/
@[stacks 052N "coordinatewise graded decomposition instance"]
noncomputable instance (priority := 100) instDecomposition :
    DirectSum.Decomposition (grading ℳ) :=
  decomposition ℳ

end Decomposition

end Pi
end GradedModule
