module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Group.Action.NatInt

/-!
# Tensor products of integer-graded modules over a naturally graded ring

This file gives the tensor product of integer-graded modules its neutral total-degree carrier.
The pure additive construction depends only on `A`, the module gradings `ℳ` and `ℵ`, and the
degree.  The keyed surface `gradingFor A 𝒜 ℳ ℵ` exposes that same carrier to graded-ring
typeclass inference when balancing over `A` is required.

The decomposition map is explicit: first decompose both inputs over `ℤ`, collect bidegrees by
their sum, and then descend the resulting additive pairing through the `A`-balanced tensor
product.  Only balance and inverse laws are proof obligations.
-/

@[expose] public section

noncomputable section

open scoped DirectSum TensorProduct

universe uA uM uN uσ

namespace GradedModule.TensorProduct

variable (A : Type uA) [CommRing A]
variable {σ : Type uσ} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [gradedRing : GradedRing 𝒜]
variable {M : Type uM} [AddCommGroup M] [Module A M]
variable {N : Type uN} [AddCommGroup N] [Module A N]
variable (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
variable [gradedSMulM : SetLike.GradedSMul 𝒜 ℳ]
variable [gradedSMulN : SetLike.GradedSMul 𝒜 ℵ]

/-- Stacks `01MK`: the neutral total-degree carrier on `M ⊗[A] N`.

The component in degree `k` is spanned over `ℤ` by pure tensors of homogeneous elements whose
degrees add to `k`.  It is independent of any chosen grading of `A`; `gradingFor` supplies the
keyed instance surface when a compatible ring grading is in scope. -/
@[stacks 01MK "total grading on a tensor product"]
def grading (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
    (k : ℤ) : Submodule ℤ (M ⊗[A] N) :=
  Submodule.span ℤ {z | ∃ (i j : ℤ) (m : ℳ i) (n : ℵ j),
    i + j = k ∧ z = (m : M) ⊗ₜ[A] (n : N)}

set_option linter.unusedVariables false in
/-- Stacks `01MK`: the neutral tensor grading keyed by the chosen ring grading for instance
search.  Its carrier is definitionally `grading A ℳ ℵ`. -/
@[reducible, stacks 01MK "ring-grading-keyed tensor grading", nolint unusedArguments]
def gradingFor (𝒜 : ℕ → σ) (ℳ : ℤ → Submodule ℤ M)
    (ℵ : ℤ → Submodule ℤ N) : ℤ → Submodule ℤ (M ⊗[A] N) := grading A ℳ ℵ

/-- Stacks `01MK`: forgetting the ring-grading key recovers the neutral tensor grading. -/
@[simp, stacks 01MK "keyed tensor grading equals neutral grading"]
theorem gradingFor_eq_grading : gradingFor A 𝒜 ℳ ℵ = grading A ℳ ℵ := sorry

/-- Stacks `01MK`: each keyed tensor component is the corresponding neutral component. -/
@[simp, stacks 01MK "keyed tensor grading component"]
theorem gradingFor_apply (k : ℤ) : gradingFor A 𝒜 ℳ ℵ k = grading A ℳ ℵ k := sorry

/-- Stacks `01MK`: homogeneous scalar multiplication acts on the neutral total tensor grading. -/
@[stacks 01MK "graded scalar action on a tensor grading"]
instance gradedSMul : SetLike.GradedSMul 𝒜 (grading A ℳ ℵ) := sorry

/-- A pure tensor of homogeneous elements belongs to the component indexed by the sum of their
degrees. -/
@[stacks 01MK "homogeneous pure tensor membership"]
theorem tmul_mem {i j : ℤ} (m : ℳ i) (n : ℵ j) :
    (m : M) ⊗ₜ[A] (n : N) ∈ grading A ℳ ℵ (i + j) := sorry

/-- Insert a homogeneous pure tensor into the direct-sum slot indexed by its total degree. -/
def componentValue (p q : ℤ) (m : ℳ p) (n : ℵ q) :
    DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) :=
  DirectSum.lof ℤ ℤ (fun k ↦ grading A ℳ ℵ k) (p + q)
    ⟨(m : M) ⊗ₜ[A] (n : N), tmul_mem A ℳ ℵ m n⟩

/-- The homogeneous component value is additive in its second input. -/
theorem componentValue_add_right (p q : ℤ) (m : ℳ p) (n₁ n₂ : ℵ q) :
    componentValue A ℳ ℵ p q m (n₁ + n₂) =
      componentValue A ℳ ℵ p q m n₁ + componentValue A ℳ ℵ p q m n₂ := sorry

/-- The homogeneous component value is `ℤ`-linear in its second input. -/
theorem componentValue_smul_right (p q : ℤ) (m : ℳ p) (r : ℤ) (n : ℵ q) :
    componentValue A ℳ ℵ p q m (r • n) =
      r • componentValue A ℳ ℵ p q m n := sorry

/-- Fixing the first homogeneous input gives the component map in the second input. -/
def componentRight (p q : ℤ) (m : ℳ p) :
    ℵ q →ₗ[ℤ] DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) where
  toFun := componentValue A ℳ ℵ p q m
  map_add' := componentValue_add_right A ℳ ℵ p q m
  map_smul' := componentValue_smul_right A ℳ ℵ p q m

/-- The right-input component map is additive in its fixed first input. -/
theorem componentRight_add (p q : ℤ) (m₁ m₂ : ℳ p) :
    componentRight A ℳ ℵ p q (m₁ + m₂) =
      componentRight A ℳ ℵ p q m₁ + componentRight A ℳ ℵ p q m₂ := sorry

/-- The right-input component map is `ℤ`-linear in its fixed first input. -/
theorem componentRight_smul (p q : ℤ) (r : ℤ) (m : ℳ p) :
    componentRight A ℳ ℵ p q (r • m) =
      r • componentRight A ℳ ℵ p q m := sorry

/-- The bilinear map inserting one homogeneous bidegree into its total-degree slot. -/
def componentPairing (p q : ℤ) :
    ℳ p →ₗ[ℤ] ℵ q →ₗ[ℤ] DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) where
  toFun := componentRight A ℳ ℵ p q
  map_add' := componentRight_add A ℳ ℵ p q
  map_smul' := componentRight_smul A ℳ ℵ p q

/-- Insert a tensor of homogeneous components into the summand indexed by the sum of their
degrees. -/
@[stacks 01MK "homogeneous bidegree component map"]
def componentMap (p q : ℤ) :
    (ℳ p ⊗[ℤ] ℵ q) →ₗ[ℤ] DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) :=
  _root_.TensorProduct.lift (componentPairing A ℳ ℵ p q)

/-- On homogeneous pure tensors, `componentMap` is the canonical total-degree inclusion. -/
@[simp, stacks 01MK "component map on a pure tensor"]
theorem componentMap_tmul (p q : ℤ) (m : ℳ p) (n : ℵ q) :
    componentMap A ℳ ℵ p q (m ⊗ₜ[ℤ] n) = componentValue A ℳ ℵ p q m n := sorry

/-- Sum the maps from all bidegrees into the total-degree direct sum. -/
@[stacks 01MK "collect tensor bidegrees by total degree"]
def pairSum :
    DirectSum (ℤ × ℤ) (fun pq ↦ ℳ pq.1 ⊗[ℤ] ℵ pq.2) →ₗ[ℤ]
      DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) :=
  DirectSum.toModule ℤ (ℤ × ℤ) _
    (fun pq ↦ componentMap A ℳ ℵ pq.1 pq.2)

variable [decompM : DirectSum.Decomposition ℳ]
variable [decompN : DirectSum.Decomposition ℵ]

/-- Decompose an unbalanced integer tensor into the direct sum of its input bidegrees. -/
@[stacks 01MK "raw tensor bidegree decomposition"]
def rawBigrade :
    (M ⊗[ℤ] N) →ₗ[ℤ]
      DirectSum (ℤ × ℤ) (fun pq ↦ ℳ pq.1 ⊗[ℤ] ℵ pq.2) :=
  (_root_.TensorProduct.directSum ℤ ℤ
      (fun p ↦ ℳ p) (fun q ↦ ℵ q)).toLinearMap.comp
    (_root_.TensorProduct.map
      (DirectSum.decomposeLinearEquiv ℳ).toLinearMap
      (DirectSum.decomposeLinearEquiv ℵ).toLinearMap)

/-- Decompose an unbalanced integer tensor and collect equal total degrees. -/
@[stacks 01MK "raw total-degree tensor decomposition"]
def rawDecompose :
    (M ⊗[ℤ] N) →ₗ[ℤ] DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) :=
  (pairSum A ℳ ℵ).comp (rawBigrade ℳ ℵ)

/-- The `ℤ`-bilinear decomposition pairing before imposing the `A`-balancing relation. -/
@[stacks 01MK "tensor decomposition pairing"]
def decomposePairing :
    M →ₗ[ℤ] N →ₗ[ℤ] DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) :=
  _root_.TensorProduct.curry (rawDecompose A ℳ ℵ)

/-- The additive pairing underlying `decomposePairing`. -/
def decomposeAddPairing :
    M →+ N →+ DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) :=
  LinearMap.toAddMonoidHom'.comp (decomposePairing A ℳ ℵ).toAddMonoidHom

include gradedRing gradedSMulM gradedSMulN

/-- The explicit additive decomposition pairing respects the balancing relation over `A`. -/
@[stacks 01MK "tensor decomposition pairing is balanced"]
theorem decomposeAddPairing_balanced :
    ∀ (a : A) (m : M) (n : N),
      decomposeAddPairing A ℳ ℵ (a • m) n =
        decomposeAddPairing A ℳ ℵ m (a • n) := sorry

/-- The explicit total-degree decomposition map on `M ⊗[A] N`.

Its data is obtained by `TensorProduct.liftAddHom` from the named additive pairing; no
decomposition is selected from an existence proof. -/
@[stacks 01MK "explicit tensor-product grading decomposition map"]
def decompose :
    (M ⊗[A] N) →ₗ[ℤ] DirectSum ℤ (fun k ↦ grading A ℳ ℵ k) :=
  (_root_.TensorProduct.liftAddHom
      (decomposeAddPairing A ℳ ℵ)
      (decomposeAddPairing_balanced A 𝒜 ℳ ℵ)).toIntLinearMap

/-- On a pure tensor, the quotient decomposition agrees with the raw integer-tensor
decomposition. -/
@[simp, stacks 01MK "tensor decomposition on pure tensors"]
theorem decompose_tmul (m : M) (n : N) :
    decompose A 𝒜 ℳ ℵ (m ⊗ₜ[A] n) =
      rawDecompose A ℳ ℵ (m ⊗ₜ[ℤ] n) := sorry

/-- The decomposition of a homogeneous pure tensor is concentrated in the sum of its degrees. -/
@[simp, stacks 01MK "homogeneous pure tensor decomposition"]
theorem decompose_tmul_of_mem {p q : ℤ} {m : M} {n : N}
    (hm : m ∈ ℳ p) (hn : n ∈ ℵ q) :
    decompose A 𝒜 ℳ ℵ (m ⊗ₜ[A] n) =
      DirectSum.lof ℤ ℤ (fun k ↦ grading A ℳ ℵ k) (p + q)
        ⟨m ⊗ₜ[A] n, tmul_mem A ℳ ℵ ⟨m, hm⟩ ⟨n, hn⟩⟩ := sorry

/-- The matching component of a homogeneous pure tensor recovers that tensor. -/
@[simp, stacks 01MK "matching component of tensor decomposition"]
theorem component_decompose_tmul {p q : ℤ} {m : M} {n : N}
    (hm : m ∈ ℳ p) (hn : n ∈ ℵ q) :
    DirectSum.component ℤ ℤ (fun k ↦ grading A ℳ ℵ k) (p + q)
        (decompose A 𝒜 ℳ ℵ (m ⊗ₜ[A] n)) =
      ⟨m ⊗ₜ[A] n, tmul_mem A ℳ ℵ ⟨m, hm⟩ ⟨n, hn⟩⟩ := sorry

/-- Every component away from the total degree of a homogeneous pure tensor vanishes. -/
@[simp, stacks 01MK "off-diagonal component of tensor decomposition"]
theorem component_decompose_tmul_of_ne {p q k : ℤ} {m : M} {n : N}
    (hm : m ∈ ℳ p) (hn : n ∈ ℵ q) (hk : k ≠ p + q) :
    DirectSum.component ℤ ℤ (fun j ↦ grading A ℳ ℵ j) k
        (decompose A 𝒜 ℳ ℵ (m ⊗ₜ[A] n)) = 0 := sorry

/-- Recomposing the explicit tensor decomposition recovers the original tensor. -/
@[stacks 01MK "tensor decomposition left inverse"]
theorem decompose_left_inv :
    DirectSum.coeLinearMap (grading A ℳ ℵ) ∘ₗ decompose A 𝒜 ℳ ℵ =
      LinearMap.id := sorry

/-- Decomposing after recomposition is the identity on the total-degree direct sum. -/
@[stacks 01MK "tensor decomposition right inverse"]
theorem decompose_right_inv :
    decompose A 𝒜 ℳ ℵ ∘ₗ DirectSum.coeLinearMap (grading A ℳ ℵ) =
      LinearMap.id := sorry

/-- The canonical direct-sum decomposition of the total tensor grading.

The `decompose'` field is definitionally the named `decompose` map; only its inverse laws are
deferred proof fields. -/
@[reducible, instance 100, stacks 01MK "tensor-product keyed grading decomposition"]
noncomputable instance decompositionFor :
    DirectSum.Decomposition (gradingFor A 𝒜 ℳ ℵ) :=
  DirectSum.Decomposition.ofLinearMap
    (gradingFor A 𝒜 ℳ ℵ) (decompose A 𝒜 ℳ ℵ)
    (decompose_left_inv A 𝒜 ℳ ℵ) (decompose_right_inv A 𝒜 ℳ ℵ)

/-- The canonical class decomposition is the named explicit tensor decomposition. -/
@[simp, stacks 01MK "named tensor decomposition agrees with the class projection"]
theorem decompose_eq (x : M ⊗[A] N) :
    DirectSum.decompose (gradingFor A 𝒜 ℳ ℵ) x = decompose A 𝒜 ℳ ℵ x := sorry

/-- The total tensor grading is internal as a consequence of its explicit decomposition. -/
@[stacks 01MK "total tensor grading is internal"]
theorem isInternal : DirectSum.IsInternal (gradingFor A 𝒜 ℳ ℵ) := sorry

end GradedModule.TensorProduct

end
