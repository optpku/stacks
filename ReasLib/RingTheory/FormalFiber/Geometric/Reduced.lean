module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import ReasLib.RingTheory.FormalFiber.FieldProperty
import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometrically reduced formal fibers

@stack 0BIW
-/

@[expose] public section

universe u v

namespace FieldAlgebraProperty

/-- Geometric reducedness, viewed as a reusable property of algebras over fields. -/
@[stacks 0BIW "geometrically reduced field-algebra property"]
abbrev geometricallyReduced : FieldAlgebraProperty.{u, v} :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦
    Algebra.IsGeometricallyReduced k A

/-- Geometric reducedness satisfies all five formal-fiber permanence laws. -/
@[stacks 0BIW "geometrically reduced formal-fiber laws"]
instance geometricallyReduced.formalFiberLaws :
    (geometricallyReduced : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry

end FieldAlgebraProperty
