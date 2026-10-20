module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Proper morphisms and field extensions

This file records descent of properness along extensions of the ground field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsProper

/-- Properness over a field descends along an arbitrary extension of the ground field. -/
theorem of_baseChangeToFieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper (FieldExtension.toBase k K f)] : IsProper f := sorry

end AlgebraicGeometry.IsProper
