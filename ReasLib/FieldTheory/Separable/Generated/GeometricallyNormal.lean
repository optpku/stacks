module

public import Mathlib.FieldTheory.Separable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated.GeometricallyReduced
public import ReasLib.RingTheory.Normal.GeometricallyNormal.Localization

/-!
# Geometric normality of separable field extensions

Separable field extensions are geometrically normal, and geometric normality
is invariant under separable algebraic changes of the ground field.
-/

@[expose] public section

namespace Algebra.IsSeparableOver

universe u v

/-- A field extension satisfying `Algebra.IsSeparableOver` is geometrically
normal over its base field. -/
@[stacks 0C30]
theorem isGeometricallyNormal
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [IsSeparableOver k K] :
    Algebra.IsGeometricallyNormal k K := sorry

end Algebra.IsSeparableOver

namespace Algebra.IsGeometricallyNormal

universe u v w

/-- Geometric normality of a `k'`-algebra is unchanged after restricting
scalars along a separable algebraic extension `k' / k`. -/
@[stacks 0C31]
theorem iff_of_isSeparable
    {k : Type u} {k' : Type v} {A : Type w}
    [Field k] [Field k'] [CommRing A]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [Algebra.IsSeparable k k'] :
    IsGeometricallyNormal k A ↔ IsGeometricallyNormal k' A := sorry

end Algebra.IsGeometricallyNormal
