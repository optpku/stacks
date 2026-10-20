module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Characteristic-zero geometric reducedness

This leaf owns the ring-level characteristic-zero specialization of
`Algebra.IsGeometricallyReduced`.  The field-extension separability statement
is kept in the field-theory owner
`ReasLib.FieldTheory.Separable.Generated.CharZero`.

@stack 0322
-/

universe u v

namespace Algebra.IsGeometricallyReduced

/-- Proposition 10.158.9 (2), tag `0322`: every field extension of a
characteristic-zero field is geometrically reduced over its base. -/
@[stacks 0322 "(2)"]
theorem of_charZero
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] [CharZero k] :
    Algebra.IsGeometricallyReduced k K := sorry

end Algebra.IsGeometricallyReduced
