module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FiniteSeparable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

/-!
# Density of finite separable field-valued points

Finite separable field-valued points are dense on algebraic spaces smooth over a
field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite separable field-valued points are dense in an algebraic space smooth
over a field. -/
theorem dense_finiteSeparableFieldPoints {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Smooth (SchemeRealization.toBase X)] :
    Dense (setOf fun x : Points X ↦ IsFiniteSeparableFieldPoint x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
