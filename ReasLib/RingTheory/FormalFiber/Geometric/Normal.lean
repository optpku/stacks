module

public import ReasLib.RingTheory.FormalFiber.FieldProperty
public import ReasLib.RingTheory.Normal.GeometricallyNormal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometrically normal formal fibers

@stack 0BIX
-/

@[expose] public section

universe u v

namespace FieldAlgebraProperty

/-- Geometric normality, viewed as a reusable property of algebras over fields. -/
@[stacks 0BIX "geometrically normal field-algebra property"]
abbrev geometricallyNormal : FieldAlgebraProperty.{u, v} :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦
    Algebra.IsGeometricallyNormal k A

/-- Geometric normality satisfies all five formal-fiber permanence laws. -/
@[stacks 0BIX "geometrically normal formal-fiber laws"]
instance geometricallyNormal.formalFiberLaws :
    (geometricallyNormal : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry

end FieldAlgebraProperty
