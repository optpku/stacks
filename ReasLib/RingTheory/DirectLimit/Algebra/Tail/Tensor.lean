/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import ReasLib.RingTheory.DirectLimit.Algebra.Tensor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products over cofinal tails

This leaf gives the tensor-product form of the canonical map from a tail stage
to a full directed direct limit.  The chosen tail base stage is explicit: it
selects the algebra actions used by the tensor products.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Tail.Tensor

variable {I : Type u} [Preorder I]
variable {A : I → Type v} [∀ i, CommRing (A i)]

/-- The canonical linear map from a tensor product over a tail stage to the
tensor product over the full direct limit. -/
@[stacks 00QV "direct-limit algebra tail tensor"]
noncomputable def toFull
    (f : ∀ i j, i ≤ j → A i →+* A j) (i0 : I)
    (X : Type w) [AddCommGroup X] [Module (A i0) X]
    (j : Set.Ici i0) :
    letI : Algebra (A i0) (A j.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
    letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i0
    A j.1 ⊗[A i0] X →ₗ[A i0]
      Ring.DirectLimit A (fun i j h ↦ f i j h) ⊗[A i0] X :=
  letI : Algebra (A i0) (A j.1) :=
    Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
  letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
    Ring.DirectLimit.Algebra.stageAlgebra f i0
  LinearMap.rTensor X
    (Ring.DirectLimit.Algebra.Tail.ofFull f i0 j).toLinearMap

/-- The tail-stage tensor map sends a pure tensor to the tensor of its image
in the full direct limit. -/
@[simp, stacks 00QV "direct-limit algebra tail tensor"]
theorem toFull_tmul
    (f : ∀ i j, i ≤ j → A i →+* A j) (i0 : I)
    (X : Type w) [AddCommGroup X] [Module (A i0) X]
    (j : Set.Ici i0) (a : A j.1) (x : X) :
    letI : Algebra (A i0) (A j.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
    letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i0
    toFull f i0 X j (a ⊗ₜ[A i0] x) =
      Ring.DirectLimit.of A (fun i j h ↦ f i j h) j.1 a ⊗ₜ[A i0] x := sorry

/-- Tensoring a tail transition and then mapping to the full limit is the
same as mapping directly from the earlier tail stage. -/
@[stacks 00QV "direct-limit algebra tail tensor"]
theorem toFull_comp_transition
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (X : Type w) [AddCommGroup X] [Module (A i0) X]
    {j k : Set.Ici i0} (hjk : j ≤ k) :
    letI : Algebra (A i0) (A j.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
    letI : Algebra (A i0) (A k.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 k
    letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i0
    (toFull f i0 X k).comp
        (LinearMap.rTensor X
          (Ring.DirectLimit.Algebra.Tail.transition f i0 hjk).toLinearMap) =
      toFull f i0 X j := sorry

/-- Applying the tail-stage tensor map after a transition has the same value
as applying it at the original stage. -/
@[simp, stacks 00QV "direct-limit algebra tail tensor"]
theorem toFull_transition
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (X : Type w) [AddCommGroup X] [Module (A i0) X]
    {j k : Set.Ici i0} (hjk : j ≤ k)
    (z :
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      A j.1 ⊗[A i0] X) :
    letI : Algebra (A i0) (A j.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
    letI : Algebra (A i0) (A k.1) :=
      Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 k
    letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      Ring.DirectLimit.Algebra.stageAlgebra f i0
    toFull f i0 X k
        (LinearMap.rTensor X
          (Ring.DirectLimit.Algebra.Tail.transition f i0 hjk).toLinearMap z) =
      toFull f i0 X j z := sorry

/-- Every tensor over the full direct limit is represented at a stage in the
tail above `i0`. -/
@[stacks 00QV "direct-limit algebra tail tensor"]
theorem exists_stage [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j) (i0 : I)
    (X : Type w) [AddCommGroup X] [Module (A i0) X]
    (z :
      letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
      Ring.DirectLimit A (fun i j h ↦ f i j h) ⊗[A i0] X) :
    ∃ j : Set.Ici i0,
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      ∃ z_j : A j.1 ⊗[A i0] X,
        toFull f i0 X j z_j = z := sorry

/-- A finite family of tensors over the full direct limit is represented at
one common tail stage. -/
@[stacks 00QV "direct-limit algebra tail tensor"]
theorem exists_stage_finset [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j) (i0 : I)
    (X : Type w) [AddCommGroup X] [Module (A i0) X]
    {K : Type*} (s : Finset K)
    (z : K →
      letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
      Ring.DirectLimit A (fun i j h ↦ f i j h) ⊗[A i0] X) :
    ∃ j : Set.Ici i0,
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      ∃ z_j : K → A j.1 ⊗[A i0] X,
        ∀ k ∈ s, toFull f i0 X j (z_j k) = z k := sorry

/-- Equality of two tensors from one tail stage in the full direct-limit
tensor product is witnessed after a later tail transition. -/
@[stacks 00QV "direct-limit algebra tail tensor"]
theorem eventuallyEq [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (X : Type w) [AddCommGroup X] [Module (A i0) X]
    {j : Set.Ici i0}
    {z z' :
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      A j.1 ⊗[A i0] X}
    (h :
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
      toFull f i0 X j z = toFull f i0 X j z') :
    ∃ k : Set.Ici i0, ∃ hjk : j ≤ k,
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      letI : Algebra (A i0) (A k.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 k
      LinearMap.rTensor X
          (Ring.DirectLimit.Algebra.Tail.transition f i0 hjk).toLinearMap z =
        LinearMap.rTensor X
          (Ring.DirectLimit.Algebra.Tail.transition f i0 hjk).toLinearMap z' := sorry

/-- A finite family of equalities in the full direct-limit tensor product is
witnessed after one common tail transition. -/
@[stacks 00QV "direct-limit algebra tail tensor"]
theorem eventuallyEq_finset [IsDirectedOrder I]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)] (i0 : I)
    (X : Type w) [AddCommGroup X] [Module (A i0) X]
    {K : Type*} (s : Finset K) {j : Set.Ici i0}
    (z z' : K →
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      A j.1 ⊗[A i0] X)
    (h : ∀ a ∈ s,
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      letI : Algebra (A i0) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
        Ring.DirectLimit.Algebra.stageAlgebra f i0
      toFull f i0 X j (z a) = toFull f i0 X j (z' a)) :
    ∃ k : Set.Ici i0, ∃ hjk : j ≤ k,
      letI : Algebra (A i0) (A j.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      letI : Algebra (A i0) (A k.1) :=
        Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 k
      ∀ a ∈ s,
        LinearMap.rTensor X
            (Ring.DirectLimit.Algebra.Tail.transition f i0 hjk).toLinearMap (z a) =
          LinearMap.rTensor X
            (Ring.DirectLimit.Algebra.Tail.transition f i0 hjk).toLinearMap (z' a) := sorry

end Ring.DirectLimit.Algebra.Tail.Tensor
