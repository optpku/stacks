module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Geometrically Regular Field Algebras

This module owns the field-algebra predicate defined by regularity after finite purely
inseparable base change.
-/

open scoped TensorProduct

namespace Algebra

universe u v w

/-- A commutative `k`-algebra is geometrically regular when every finite purely inseparable
field extension of `k` gives a regular tensor base-change ring. -/
@[stacks 0382]
class IsGeometricallyRegular (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] : Prop where
  /-- Regularity after a finite purely inseparable field extension of the base. -/
  isRegularRing_baseChange (K : Type (max u v)) [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsPurelyInseparable k K] :
    IsRegularRing (K ⊗[k] A)

attribute [instance] IsGeometricallyRegular.isRegularRing_baseChange

namespace IsGeometricallyRegular

/-- Geometric regularity is equivalent to regularity after every finite purely inseparable tensor
base change. -/
@[stacks 0382]
theorem iff_tensorRegular
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] :
    IsGeometricallyRegular k A ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K]
        [FiniteDimensional k K] [IsPurelyInseparable k K], IsRegularRing (K ⊗[k] A) := sorry

/-- A finite purely inseparable base change in any universe is regular. This
is the universe-polymorphic consumer API for `IsGeometricallyRegular`. -/
@[stacks 0382 "arbitrary-universe geometrically regular base change"]
theorem tensorProduct_isRegularRing
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [IsGeometricallyRegular k A] (K : Type w) [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] :
    IsRegularRing (K ⊗[k] A) := sorry

attribute [instance] tensorProduct_isRegularRing

end IsGeometricallyRegular

/-- A field is geometrically regular over itself. -/
instance instIsGeometricallyRegularSelf (k : Type u) [Field k] :
    IsGeometricallyRegular k k := sorry

/-- A geometrically regular algebra over a field is a regular ring. -/
theorem isRegularRing_of_isGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsGeometricallyRegular k A] : IsRegularRing A := sorry

end Algebra
