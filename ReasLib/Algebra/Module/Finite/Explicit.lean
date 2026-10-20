module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness for an explicit module action

This module records finite generation while keeping the scalar action as
explicit data instead of installing it as a typeclass instance.
-/

@[expose] public section

universe u v

namespace Module

/-- A module is finite for the specified scalar action. -/
@[stacks 0897 "finite module for an explicit scalar action"]
def FiniteWithAction
    (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M]
    (moduleAction : Module R M) : Prop :=
  @Module.Finite R M _ _ moduleAction

/-- Explicit-action finiteness is the ordinary finite-module predicate evaluated at that
action. -/
@[stacks 0897 "explicit-action finite module specification"]
theorem finiteWithAction_iff
    (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M]
    (moduleAction : Module R M) :
    FiniteWithAction R M moduleAction ↔ @Module.Finite R M _ _ moduleAction :=
  Iff.rfl

end Module
