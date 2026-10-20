module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced

/-!
# Geometric reducedness after finite purely inseparable extension

This leaf records the existence of a finite purely inseparable extension over
which the reduction of a finite-component scheme becomes geometrically reduced.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

namespace geometricallyReduced

/-- A scheme locally of finite type over a field with finitely many irreducible
components becomes geometrically reduced after reduction and a suitable finite
purely inseparable extension of the base field. -/
@[stacks 04KT]
theorem exists_finitePurelyInseparableExtension
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [Finite (irreducibleComponents X.left)] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
      geometricallyReduced (FieldExtension.Reduced.baseChange k k' X) := sorry

end geometricallyReduced

end AlgebraicGeometry.SchemeOverField
