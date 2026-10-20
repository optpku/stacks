module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometric reducedness and separable algebraic base change

This leaf contains the ring-side invariance statement for geometric reducedness.
It deliberately depends only on the canonical `Algebra.IsSeparable` predicate;
the Stacks-specific `Algebra.IsSeparableOver` interface belongs to the field-theory
leaves and is not needed here.

@stack 0C2Y
-/

@[expose] public section

universe u v w

namespace Algebra.IsGeometricallyReduced

/-- Lemma 10.43.9 (Tag 0C2Y): geometric reducedness of a commutative algebra is invariant under
restricting scalars along a separable algebraic extension of the ground field. -/
@[stacks 0C2Y]
theorem iff_of_isSeparable
    {k : Type u} {k' : Type v} {A : Type w}
    [Field k] [Field k'] [CommRing A]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra.IsSeparable k k'] :
    IsGeometricallyReduced k A ↔ IsGeometricallyReduced k' A := sorry

end Algebra.IsGeometricallyReduced
