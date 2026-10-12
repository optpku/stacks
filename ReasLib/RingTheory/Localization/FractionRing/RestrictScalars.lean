/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fraction rings under scalar restriction

This leaf records that restricting the scalar ring of a subalgebra in a fixed
ambient semifield does not change its fraction-ring structure.  The result is
an explicit theorem rather than an instance because scalar restriction is a
chosen presentation of the same subalgebra.
-/

@[expose] public section

namespace IsFractionRing

universe u v w

/-- Restricting scalars of a subalgebra preserves its fraction-ring structure
in the fixed ambient semifield. -/
@[stacks 07ND "fraction rings under scalar restriction"]
theorem restrictScalars
    {k : Type u} {B : Type v} {K : Type w}
    [CommSemiring k] [CommSemiring B] [Semifield K]
    [Algebra k B] [Algebra B K] [Algebra k K] [IsScalarTower k B K]
    (C : Subalgebra B K) [IsFractionRing C K] :
    IsFractionRing (C.restrictScalars k) K := sorry

end IsFractionRing
