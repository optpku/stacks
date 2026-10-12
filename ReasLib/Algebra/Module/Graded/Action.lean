/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded scalar actions along linear maps

This leaf contains the map and preimage constructions for internally graded scalar actions.
They are independent of quotients; quotient-specific grading families import this support and
specialize it to their canonical quotient maps.
-/

@[expose] public section

universe uA uB uR uM uQ uS

namespace Submodule

variable {ιA : Type uA} {ιB : Type uB} [VAdd ιA ιB]
variable {R : Type uR} [Semiring R]
variable {A : Type uS} {S : Type*} [SetLike S A]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {Q : Type uQ} [AddCommMonoid Q] [Module R Q]
variable [SMul A M] [SMul A Q]

/-- Homogeneous scalar multiplication descends along a scalar-compatible linear
map, component by component. -/
@[stacks 052N "mapped graded scalar action membership"]
theorem map_grading_smul_mem
    (𝒜 : ιA → S) (ℳ : ιB → Submodule R M) (q : M →ₗ[R] Q)
    [SetLike.GradedSMul 𝒜 ℳ]
    (hq : ∀ (a : A) (x : M), q (a • x) = a • q x)
    {i : ιA} {j : ιB} {a : A} {x : Q}
    (ha : a ∈ 𝒜 i) (hx : x ∈ (ℳ j).map q) :
    a • x ∈ (ℳ (i +ᵥ j)).map q := sorry

/-- The image family of a scalar-compatible linear map inherits the graded scalar
action. -/
@[reducible, stacks 052N "mapped graded scalar action"]
def mapGradedSMul
    (𝒜 : ιA → S) (ℳ : ιB → Submodule R M) (q : M →ₗ[R] Q)
    [SetLike.GradedSMul 𝒜 ℳ]
    (hq : ∀ (a : A) (x : M), q (a • x) = a • q x) :
    SetLike.GradedSMul 𝒜 (fun i ↦ (ℳ i).map q) where
  smul_mem := fun i j a x ha hx ↦ map_grading_smul_mem 𝒜 ℳ q hq ha hx

/-- Homogeneous scalar multiplication is preserved by the preimage of a
scalar-compatible linear map. -/
@[stacks 052N "comapped graded scalar action membership"]
theorem comap_grading_smul_mem
    (𝒜 : ιA → S) (𝒩 : ιB → Submodule R Q) (f : M →ₗ[R] Q)
    [SetLike.GradedSMul 𝒜 𝒩]
    (hf : ∀ (a : A) (x : M), f (a • x) = a • f x)
    {i : ιA} {j : ιB} {a : A} {x : M}
    (ha : a ∈ 𝒜 i) (hx : x ∈ (𝒩 j).comap f) :
    a • x ∈ (𝒩 (i +ᵥ j)).comap f := sorry

/-- The preimage family of a scalar-compatible linear map inherits the graded
scalar action. -/
@[reducible, stacks 052N "comapped graded scalar action"]
def comapGradedSMul
    (𝒜 : ιA → S) (𝒩 : ιB → Submodule R Q) (f : M →ₗ[R] Q)
    [SetLike.GradedSMul 𝒜 𝒩]
    (hf : ∀ (a : A) (x : M), f (a • x) = a • f x) :
    SetLike.GradedSMul 𝒜 (fun i ↦ (𝒩 i).comap f) where
  smul_mem := fun i j a x ha hx ↦ comap_grading_smul_mem 𝒜 𝒩 f hf ha hx

end Submodule
