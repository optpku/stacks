/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.FormalFiber.FieldProperty

@[expose] public section

/-!
# Cohen-Macaulay Formal Fibers

@stack 0BJ9

Cohen-Macaulayness is a property of the algebra ring itself, independent of the displayed ground
field.  This file exposes that predicate and its complete formal-fiber law instance.
-/

universe u v

namespace FieldAlgebraProperty

/-- Cohen-Macaulayness, viewed as a property of algebras over fields. -/
@[stacks 0BJ9 "Cohen-Macaulay field-algebra property"]
abbrev cohenMacaulay : FieldAlgebraProperty.{u, v} :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ CohenMacaulayRing A

/-- Cohen-Macaulayness satisfies the five formal-fiber permanence laws. -/
@[stacks 0BJ9 "Cohen-Macaulay formal-fiber laws"]
instance cohenMacaulay.formalFiberLaws :
    (cohenMacaulay : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry

end FieldAlgebraProperty
