/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.Isomorphism
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bijectivity over a cofinal tail

This is the source-facing tail adapter for the fixed-base finitely presented
isomorphism theorem.  It keeps the canonical stage algebra selected by the
initial stage and exposes the later stage as a subtype of `Set.Ici i0`.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

noncomputable section

namespace Ring.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Isomorphism

variable {I : Type u} [Preorder I] [IsDirectedOrder I]
variable (G : I → Type v) [∀ i, CommRing (G i)]
variable (f : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G (fun i j h ↦ f i j h)]
variable (i0 : I)
variable {B C : Type w} [CommRing B] [CommRing C]
variable [Algebra (G i0) B] [Algebra (G i0) C]

local notation "G∞" => Ring.DirectLimit G (fun i j h ↦ f i j h)

/-- Stacks tag `0C32`: bijectivity of the base change of a finitely presented
map to the full direct limit is witnessed on a cofinal tail. -/
@[stacks 0C32 "finitely presented tail base-change descent"]
theorem exists_stage
    (φ : B →ₐ[G i0] C)
    (hbijective :
      letI : Algebra (G i0) G∞ := Ring.DirectLimit.Algebra.stageAlgebra f i0
      Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id (G i0) G∞)))
    (hfinitePresentation : φ.FinitePresentation) :
    ∃ j : Set.Ici i0,
      letI : Algebra (G i0) (G j.1) := Ring.DirectLimit.Algebra.Tail.stageAlgebra f i0 j
      Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id (G i0) (G j.1))) := sorry

end Ring.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Isomorphism
