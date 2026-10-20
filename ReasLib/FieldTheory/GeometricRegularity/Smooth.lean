module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.RingTheory.Smooth.Regularity

/-!
# Smooth Geometrically Regular Field Algebras

This leaf records smooth ascent of geometric regularity over a field and the
canonical field-base specialization.

@stack 07QF
-/

@[expose] public section

namespace Algebra.IsGeometricallyRegular

universe u v w

/-- Lemma 10.166.4, tag `07QF`: a smooth algebra over a geometrically regular field algebra is
geometrically regular over the original field. -/
@[stacks 07QF "smooth ascent of geometric regularity"]
theorem of_smooth
    {k : Type u} {A : Type v} {B : Type w} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Algebra.Smooth A B] [IsGeometricallyRegular k A] :
    IsGeometricallyRegular k B := sorry

end Algebra.IsGeometricallyRegular

namespace Algebra.Smooth

universe u v

/-- A smooth algebra over a field is geometrically regular over that field. -/
@[stacks 07QF "smooth field algebras are geometrically regular"]
theorem isGeometricallyRegular_of_field
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] :
    IsGeometricallyRegular k A := sorry

/-- The canonical geometric-regularity instance for a smooth field algebra. -/
@[stacks 07QF "smooth field algebra instance"]
instance instIsGeometricallyRegular_of_field
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] :
    IsGeometricallyRegular k A := sorry

end Algebra.Smooth

#synth Algebra.IsGeometricallyRegular ℚ ℚ
