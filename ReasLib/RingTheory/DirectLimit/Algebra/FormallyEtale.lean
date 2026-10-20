/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Base
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal etaleness of algebra direct limits

The reusable result is expressed for `Algebra.FormallyEtale`; the equivalent
ring-hom statement is provided as a source-facing bridge.

@stack 031N
-/

@[expose] public section

universe u v w

namespace Ring.DirectLimit

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (S : I → Type w) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
variable (φ : ∀ i j, i ≤ j → S i →ₐ[R] S j)

local notation "ρ" => fun i j h ↦ (φ i j h : S i →+* S j)

/-- A directed direct limit of formally etale commutative `R`-algebras is
formally etale over `R`. -/
@[stacks 031N "formally etale direct limit"]
theorem formallyEtale
    (hEt : ∀ i, Algebra.FormallyEtale R (S i)) :
    Algebra.FormallyEtale R (Ring.DirectLimit S ρ) := sorry

/-- The ring map from the fixed base ring to a directed direct limit is
formally etale when every stage structure map is formally etale. -/
@[stacks 031N "formally etale direct limit"]
theorem formallyEtale_algebraMap
    (hEt : ∀ i, (_root_.Algebra.algebraMap R (S i)).FormallyEtale) :
    (_root_.Algebra.algebraMap R (Ring.DirectLimit S ρ)).FormallyEtale := sorry

end Ring.DirectLimit
