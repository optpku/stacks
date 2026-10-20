/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stage algebras on cofinal tails

This leaf owns the base-stage algebra structures and algebra-valued transition
maps for a cofinal tail.  The companion Colimit leaf owns the tail
direct-limit maps and equivalences.
-/

@[expose] public section

universe u v

noncomputable section

namespace Ring.DirectLimit.Algebra.Tail

variable {I : Type u} [Preorder I]
variable {A : I → Type v} [∀ i, CommRing (A i)]

/-- A stage of the tail above `i0` is canonically an algebra over the base
stage through the transition map out of `i0`. -/
@[reducible, stacks 00QV "direct-limit algebra tail"]
noncomputable def stageAlgebra
    (f : ∀ i j, i ≤ j → A i →+* A j) (i0 : I) (j : Set.Ici i0) :
    Algebra (A i0) (A j.1) :=
  (f i0 j.1 j.2).toAlgebra

/-- The scalar map of `stageAlgebra` is the transition from the tail base
stage. -/
@[stacks 00QV "direct-limit algebra tail"]
theorem stageAlgebra_algebraMap
    (f : ∀ i j, i ≤ j → A i →+* A j) (i0 : I) (j : Set.Ici i0) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    algebraMap (A i0) (A j.1) = f i0 j.1 j.2 := sorry

/-- The algebra structures on two stages of a tail form a scalar tower along
the transition between those stages. -/
@[stacks 00QV "direct-limit algebra tail"]
theorem stageAlgebra_isScalarTower
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)]
    (i0 : I) (j k : Set.Ici i0) (hjk : j ≤ k) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0) (A k.1) := stageAlgebra f i0 k
    letI : Algebra (A j.1) (A k.1) := (f j.1 k.1 hjk).toAlgebra
    IsScalarTower (A i0) (A j.1) (A k.1) := sorry

/-- A transition inside a tail, viewed as an algebra homomorphism over the
tail base stage. -/
@[stacks 00QV "direct-limit algebra tail"]
noncomputable def transition
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)]
    (i0 : I) {j k : Set.Ici i0} (hjk : j ≤ k) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0) (A k.1) := stageAlgebra f i0 k
    A j.1 →ₐ[A i0] A k.1 :=
  letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
  letI : Algebra (A i0) (A k.1) := stageAlgebra f i0 k
  { toRingHom := f j.1 k.1 hjk
    commutes' := sorry }

/-- Forgetting the algebra structure on a tail transition recovers the
underlying transition map of the original directed system. -/
@[simp, stacks 00QV "direct-limit algebra tail"]
theorem transition_toRingHom
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)]
    (i0 : I) {j k : Set.Ici i0} (hjk : j ≤ k) :
    letI : Algebra (A i0) (A j.1) := stageAlgebra f i0 j
    letI : Algebra (A i0) (A k.1) := stageAlgebra f i0 k
    (transition f i0 hjk : A j.1 →+* A k.1) = f j.1 k.1 hjk := sorry

/-- A tail transition evaluates on an element by the underlying ring
transition map. -/
@[simp, stacks 00QV "direct-limit algebra tail"]
theorem transition_apply
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h ↦ f i j h)]
    (i0 : I) {j k : Set.Ici i0} (hjk : j ≤ k) (x : A j.1) :
    transition f i0 hjk x = f j.1 k.1 hjk x := sorry

end Ring.DirectLimit.Algebra.Tail
