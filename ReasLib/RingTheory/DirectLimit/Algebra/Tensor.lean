module

public import ReasLib.RingTheory.DirectLimit.Algebra.Base
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products over fixed-base direct limits

This leaf gives the canonical maps from tensor products over individual stages
to the tensor product over the direct limit of a system of commutative
algebras.  The maps are defined through `Ring.DirectLimit.ofAlgHom`, so no
stage-dependent algebra structure is installed globally.

@stack 05LI
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z

noncomputable section

namespace Ring.DirectLimit

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I]
variable (R : I → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)

local notation "ρ" => fun i j h ↦ (f i j h : R i →+* R j)

/-- The canonical map from a tensor product over a stage to the tensor product
over the direct limit of a fixed-base algebra system. -/
@[stacks 05LI "direct-limit tensor stage map"]
noncomputable def stageTensorMap [IsDirectedOrder I]
    (X : Type x) [AddCommGroup X] [Module A X] (i : I) :
    R i ⊗[A] X →ₗ[A] Ring.DirectLimit R ρ ⊗[A] X :=
  LinearMap.rTensor X (Ring.DirectLimit.ofAlgHom R f i).toLinearMap

/-- `stageTensorMap` sends a pure tensor to the tensor obtained by applying
the canonical map from its stage into the direct limit. -/
@[simp, stacks 05LI "direct-limit tensor stage map"]
theorem stageTensorMap_tmul [IsDirectedOrder I]
    (X : Type x) [AddCommGroup X] [Module A X] (i : I) (r : R i) (x : X) :
    stageTensorMap R f X i (r ⊗ₜ[A] x) =
      Ring.DirectLimit.of R ρ i r ⊗ₜ[A] x := sorry

/-- Transporting a tensor along a transition map before mapping to the direct
limit agrees with mapping it from its original stage. -/
@[stacks 05LI "direct-limit tensor stage map"]
theorem stageTensorMap_comp_transition [IsDirectedOrder I]
    (X : Type x) [AddCommGroup X] [Module A X]
    {i j : I} (hij : i ≤ j) :
    (stageTensorMap R f X j).comp
        (LinearMap.rTensor X (f i j hij).toLinearMap) =
      stageTensorMap R f X i := sorry

/-- Transporting a tensor along a transition map before mapping to the direct
limit agrees with mapping it from its original stage. -/
@[simp, stacks 05LI "direct-limit tensor stage map"]
theorem stageTensorMap_transition [IsDirectedOrder I]
    (X : Type x) [AddCommGroup X] [Module A X]
    {i j : I} (hij : i ≤ j) (z : R i ⊗[A] X) :
    stageTensorMap R f X j
        (LinearMap.rTensor X (f i j hij).toLinearMap z) =
      stageTensorMap R f X i z := sorry

/-- The stage-to-direct-limit tensor maps commute with base change of an
`A`-linear map in the second tensor factor. -/
@[stacks 05LI "direct-limit tensor stage map"]
theorem stageTensorMap_naturality [IsDirectedOrder I]
    {X : Type x} [AddCommGroup X] [Module A X]
    {Y : Type y} [AddCommGroup Y] [Module A Y]
    (g : X →ₗ[A] Y) (i : I) (z : R i ⊗[A] X) :
    stageTensorMap R f Y i ((g.baseChange (R i)) z) =
      (g.baseChange (Ring.DirectLimit R ρ)) (stageTensorMap R f X i z) := sorry

/-- Every tensor over a directed direct limit is represented by a tensor over
one of its stages. -/
@[stacks 05LI "direct-limit tensor descent"]
theorem exists_stageTensorMap [IsDirectedOrder I]
    (X : Type x) [AddCommGroup X] [Module A X]
    (z : Ring.DirectLimit R ρ ⊗[A] X) :
    ∃ i : I, ∃ z_i : R i ⊗[A] X,
      stageTensorMap R f X i z_i = z := sorry

/-- Equality of two tensors from one stage in the direct-limit tensor product
is already witnessed after passing to a sufficiently large stage. -/
@[stacks 05LI "direct-limit tensor descent"]
theorem eventuallyEqStageTensorMap [IsDirectedOrder I]
    [DirectedSystem R ρ]
    (X : Type x) [AddCommGroup X] [Module A X]
    {i : I} {z z' : R i ⊗[A] X}
    (h : stageTensorMap R f X i z = stageTensorMap R f X i z') :
    ∃ j : I, ∃ hij : i ≤ j,
      LinearMap.rTensor X (f i j hij).toLinearMap z =
        LinearMap.rTensor X (f i j hij).toLinearMap z' := sorry

/-- A finite family of tensors over a directed direct limit is represented at
a single common stage. -/
@[stacks 05LI "direct-limit tensor descent"]
theorem exists_stageTensorMap_finset [IsDirectedOrder I]
    (X : Type x) [AddCommGroup X] [Module A X]
    {K : Type y}
    (s : Finset K) (z : K → Ring.DirectLimit R ρ ⊗[A] X) :
    ∃ i : I, ∃ z_i : K → R i ⊗[A] X,
      ∀ k ∈ s, stageTensorMap R f X i (z_i k) = z k := sorry

/-- A finite family of equalities in a direct-limit tensor product is already
witnessed after passing to a single sufficiently large stage. -/
@[stacks 05LI "direct-limit tensor descent"]
theorem eventuallyEqStageTensorMap_finset [IsDirectedOrder I]
    [DirectedSystem R ρ]
    (X : Type x) [AddCommGroup X] [Module A X]
    {K : Type y}
    (s : Finset K) {i : I}
    (x y : K → R i ⊗[A] X)
    (hxy : ∀ k ∈ s,
      stageTensorMap R f X i (x k) = stageTensorMap R f X i (y k)) :
    ∃ j : I, ∃ hij : i ≤ j,
      ∀ k ∈ s,
        LinearMap.rTensor X (f i j hij).toLinearMap (x k) =
          LinearMap.rTensor X (f i j hij).toLinearMap (y k) := sorry

end Ring.DirectLimit
