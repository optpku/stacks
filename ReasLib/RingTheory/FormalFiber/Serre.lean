module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.FormalFiber.FieldProperty

@[expose] public section

/-!
# Serre Conditions on Formal Fibers

@stack 0BIY

Serre's condition `(S_n)` is exposed as a universe-polymorphic field-algebra property.  Its
formal-fiber laws remain a same-universe instance, matching the current generic `P`-ring machine.
-/

universe u v

namespace FieldAlgebraProperty

/-- Serre's condition `(S_n)`, viewed as a property of algebras over fields. -/
@[stacks 0BIY "Serre S field-algebra property"]
abbrev serreConditionS (n : ℕ) : FieldAlgebraProperty.{u, v} :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ SerreConditionS A n

/-- Serre's condition `(S_n)` satisfies the five formal-fiber permanence laws. -/
@[stacks 0BIY "Serre condition formal-fiber laws"]
instance serreConditionS.formalFiberLaws (n : ℕ) :
    (serreConditionS n : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry

end FieldAlgebraProperty
