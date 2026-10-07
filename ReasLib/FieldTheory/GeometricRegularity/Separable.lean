module

public import ReasLib.FieldTheory.GeometricRegularity.Directed
public import Mathlib.FieldTheory.Separable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Separable Changes of the Base Field

Geometric regularity is invariant under separable algebraic changes of its
ground field.  The API is attached to the geometric-regularity owner so that
consumers need not import the Chapter 10 source proof.

@stack 07QH
-/

@[expose] public section

namespace Algebra.IsGeometricallyRegular

universe u v w

/-- Lemma 10.166.6, tag `07QH`: for a separable algebraic field extension `k' / k`,
a `k'`-algebra `A` is geometrically regular over `k` if and only if it is geometrically
regular over `k'`. -/
@[stacks 07QH]
theorem iff_of_isSeparable
    {k : Type u} {k' : Type u} {A : Type w}
    [Field k] [Field k'] [CommRing A]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra.IsSeparable k k'] :
    IsGeometricallyRegular k A ↔ IsGeometricallyRegular k' A := sorry

end Algebra.IsGeometricallyRegular
