/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Domains in directed ring colimits

This leaf owns the integral-domain structure on a directed colimit of integral
domains.  It is independent of valuation theory.

@stack 0AS4
-/

@[expose] public section

universe u v

namespace Ring.DirectLimit

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (A : I → Type u) [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)]
variable (φ : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (φ · · ·)]

/-- A directed colimit of integral domains is an integral domain. -/
@[stacks 0AS4 "direct-limit domain component"]
instance isDomain :
    IsDomain (Ring.DirectLimit A (fun i j h ↦ φ i j h)) := sorry

end Ring.DirectLimit
