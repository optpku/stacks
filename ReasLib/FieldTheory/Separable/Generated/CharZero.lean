/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated.Properties

@[expose] public section

/-!
# Characteristic-zero separability of field extensions

This leaf owns the characteristic-zero specialization of the separable-over
field-extension API.  The corresponding ring-level geometric-reducedness
specialization is owned by
`ReasLib.RingTheory.Nilpotent.GeometricallyReduced.CharZero`.

@stack 0322
-/

universe u v

namespace Algebra.IsSeparableOver

/-- Proposition 10.158.9 (1), tag `0322`: every field extension of a
characteristic-zero field is separable over its base in the Stacks-project
sense. -/
@[stacks 0322 "(1)"]
theorem of_charZero
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] [CharZero k] :
    Algebra.IsSeparableOver k K := Algebra.IsSeparableOver.of_perfectField

end Algebra.IsSeparableOver
