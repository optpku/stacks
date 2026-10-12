/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Universe Lifts of Noetherian Rings

This leaf provides the canonical Noetherian-ring instance on a universe lift.
It is structural transport across `ULift.ringEquiv`, so it is reusable without
selecting any algebra or module structure.

@stack 0523
-/

universe u v

namespace ULift

/-- A universe lift of a Noetherian semiring is canonically Noetherian. -/
@[stacks 0523 "Noetherian rings under universe lift"]
instance instIsNoetherianRing {R : Type u} [Semiring R] [IsNoetherianRing R] :
    IsNoetherianRing (ULift.{v} R) := sorry

/-- The Noetherian-ring property is invariant under universe lift. -/
@[stacks 0523 "Noetherian rings invariant under universe lift"]
theorem isNoetherianRing_iff {R : Type u} [Semiring R] :
    IsNoetherianRing (ULift.{v} R) ↔ IsNoetherianRing R := sorry

end ULift
