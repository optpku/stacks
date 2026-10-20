/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation
public import ReasLib.RingTheory.RingHom.Syntomic.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Syntomicity after finitely presented direct-limit base change

This leaf keeps syntomic descent separate from the relative-global-complete-
intersection property used in its construction.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

noncomputable section

namespace Ring.DirectLimit.Algebra.BaseChange.FinitePresentation.Syntomic

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {R : I → Type w} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i →+* R j))]

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))

/-- Stacks tag `0C33` (2): syntomicity of the base change of a finitely
presented algebra map to a directed colimit is witnessed at one stage. -/
@[stacks 0C33 "syntomic algebra-map descent"]
theorem exists_stage
    {B C : Type x} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (φ : B →ₐ[A] C)
    (hfinitePresentation : φ.FinitePresentation)
    (hsyntomic : (Algebra.TensorProduct.map φ (AlgHom.id A R∞)).toRingHom.Syntomic) :
    ∃ i : I, (Algebra.TensorProduct.map φ (AlgHom.id A (R i))).toRingHom.Syntomic := sorry

end Ring.DirectLimit.Algebra.BaseChange.FinitePresentation.Syntomic
