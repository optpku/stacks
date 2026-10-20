/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms after finitely presented direct-limit base change

This leaf gives the ring-map counterpart of the finitely presented module
descent API.  It concerns a fixed-base system of commutative algebras and a
finitely presented map between two fixed algebras over that base.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

noncomputable section

namespace Ring.DirectLimit.Algebra.BaseChange.FinitePresentation.Isomorphism

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {R : I → Type w} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i →+* R j))]

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ (f i j h : R i →+* R j))

/-- Stacks tag `0C32`: a finitely presented algebra map whose direct-limit
base change is bijective is already bijective after base change to one stage. -/
@[stacks 0C32 "finitely presented algebra-map descent"]
theorem exists_stage
    {B C : Type x} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (φ : B →ₐ[A] C)
    (hbijective : Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id A R∞)))
    (hfinitePresentation : φ.FinitePresentation) :
    ∃ i : I, Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id A (R i))) := sorry

end Ring.DirectLimit.Algebra.BaseChange.FinitePresentation.Isomorphism
