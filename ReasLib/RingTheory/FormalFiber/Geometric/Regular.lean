/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.GeometricRegularity.Separable
public import ReasLib.RingTheory.FormalFiber.FieldProperty

/-!
# Geometrically Regular Formal Fibers

@stack 07PN

This leaf packages geometric regularity as a field-algebra property together with its
formal-fiber permanence laws.
-/

@[expose] public section

universe u v

namespace FieldAlgebraProperty

/-- Geometric regularity, viewed as a reusable property of algebras over fields. -/
@[stacks 07PN "geometrically regular field-algebra property"]
abbrev geometricallyRegular : FieldAlgebraProperty.{u, v} :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦
    Algebra.IsGeometricallyRegular k A

/-- Geometric regularity satisfies all five formal-fiber permanence laws. -/
@[stacks 07PN "geometrically regular formal-fiber laws"]
instance geometricallyRegular.formalFiberLaws :
    (geometricallyRegular : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry

end FieldAlgebraProperty
