/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Smoothness after finitely presented direct-limit base change

This leaf isolates smoothness from the other geometric properties that can be
detected after base change to a directed colimit.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

noncomputable section

namespace Ring.DirectLimit.Algebra.BaseChange.FinitePresentation.Smooth

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {R : I → Type w} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i →+* R j))]

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))

/-- Stacks tag `0C0B`: smoothness of the base change of a finitely presented
algebra map to a directed colimit is witnessed at one stage. -/
@[stacks 0C0B "smooth algebra-map descent"]
theorem exists_stage
    {B C : Type x} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (φ : B →ₐ[A] C)
    (hfinitePresentation : φ.FinitePresentation)
    (hsmooth : (Algebra.TensorProduct.map φ (AlgHom.id A R∞)).Smooth) :
    ∃ i : I, (Algebra.TensorProduct.map φ (AlgHom.id A (R i))).Smooth := sorry

end Ring.DirectLimit.Algebra.BaseChange.FinitePresentation.Smooth
