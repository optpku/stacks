/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coordinates of a graded scalar action

This leaf owns the convolution-coordinate statements for a scalar action on a direct-sum graded
module.  The core theorems use a unique-fibre hypothesis at the requested degree; the cancellation
corollaries are convenience surfaces for the common additive-action cases.  Keeping this separate
from `GradedModule.MapsTo` avoids confusing a decomposition calculation with map data.
-/

@[expose] public section

noncomputable section

universe i j u v a b

namespace DirectSum

variable {ιA : Type i} {ιM : Type j} {A : Type u} {M : Type v}
variable {σA : Type a} {σM : Type b}
variable [DecidableEq ιM] [VAdd ιA ιM]
variable [AddCommMonoid M]
variable [SetLike σM M] [AddSubmonoidClass σM M]

/-- Stacks `052N`: if a scalar is homogeneous, only the corresponding module component can
contribute to a specified target degree.  The explicit unique-fibre condition is the weakest
assumption and does not impose cancellation on the whole indexing action. -/
@[stacks 052N "graded scalar coordinate from a homogeneous scalar"]
theorem coe_decompose_smul_of_left_mem
    [DistribSMul A M]
    [SetLike σA A] (𝒜 : ιA → σA) (ℳ : ιM → σM)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {i : ιA} {j : ιM} {n : ιM} {a : A} (ha : a ∈ 𝒜 i) (m : M)
    (huniq : ∀ j', i +ᵥ j' = n ↔ j' = j) :
    (decompose ℳ (a • m) n : M) = a • (decompose ℳ m j : M) := sorry

/-- Stacks `052N`: cancellation-specialized form of
`coe_decompose_smul_of_left_mem`, with the target degree written in the usual `i +ᵥ j` form. -/
@[stacks 052N "graded scalar coordinate left homogeneous corollary"]
theorem coe_decompose_smul_vadd_of_left_mem
    [DistribSMul A M]
    [SetLike σA A] (𝒜 : ιA → σA) (ℳ : ιM → σM)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [IsLeftCancelVAdd ιA ιM]
    {i : ιA} {j : ιM} {a : A} (ha : a ∈ 𝒜 i) (m : M) :
    (decompose ℳ (a • m) (i +ᵥ j) : M) = a • (decompose ℳ m j : M) := sorry

/-- Stacks `052N`: if a vector is homogeneous, the scalar component in the unique matching fibre
is the only contribution to a specified target degree. -/
@[stacks 052N "graded scalar coordinate from a homogeneous vector"]
theorem coe_decompose_smul_of_right_mem
    [Semiring A] [Module A M] [DecidableEq ιA]
    [SetLike σA A] [AddSubmonoidClass σA A]
    (𝒜 : ιA → σA) (ℳ : ιM → σM)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ]
    {i : ιA} {j : ιM} {n : ιM} {a : A} (m : M) (hm : m ∈ ℳ j)
    (huniq : ∀ i', i' +ᵥ j = n ↔ i' = i) :
    (decompose ℳ (a • m) n : M) = (decompose 𝒜 a i : A) • m := sorry

/-- Stacks `052N`: cancellation-specialized form of
`coe_decompose_smul_of_right_mem`, with the target degree written in the usual `i +ᵥ j` form. -/
@[stacks 052N "graded scalar coordinate right homogeneous corollary"]
theorem coe_decompose_smul_vadd_of_right_mem
    [Semiring A] [Module A M] [DecidableEq ιA]
    [SetLike σA A] [AddSubmonoidClass σA A]
    (𝒜 : ιA → σA) (ℳ : ιM → σM)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ]
    [IsCancelVAdd ιA ιM]
    {i : ιA} {j : ιM} {a : A} (m : M) (hm : m ∈ ℳ j) :
    (decompose ℳ (a • m) (i +ᵥ j) : M) = (decompose 𝒜 a i : A) • m := sorry

end DirectSum

end
