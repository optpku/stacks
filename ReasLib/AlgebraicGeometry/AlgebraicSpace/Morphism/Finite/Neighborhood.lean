module

public import Mathlib.Data.Finite.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality

/-!
# Finite neighbourhoods of quasi-finite fibres of proper morphisms

A proper morphism of algebraic spaces that is quasi-finite at every point
over a given point of the target is finite over some open neighbourhood of
that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper morphism of algebraic spaces over a scheme that is quasi-finite
at every point above a point of the target is finite after restriction to
some open neighbourhood of that point. The neighbourhood is represented by
an open immersion, and the restriction is the canonical inverse-image
projection. -/
@[stacks 0A4Y]
theorem exists_isFinite_openInverseImageTo_of_quasiFiniteAt_fiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (y : Points Y)
    (h : ∀ x : Points X, Points.map f x = y → QuasiFiniteAt f x) :
    ∃ (V : AlgebraicSpace S) (ι : V ⟶ Y) (hι : IsOpenImmersion ι),
      y ∈ Set.range (Points.map ι) ∧ IsFinite (openInverseImageTo f ι) :=
  sorry

/-- A proper morphism of algebraic spaces with locally Noetherian target and
finite geometric fibre is finite over an open neighbourhood of that geometric
point. The neighbourhood is represented by an open immersion, and the
restriction is the canonical inverse-image projection. -/
@[stacks 0A4W]
theorem exists_isFinite_openInverseImageTo_of_finite_fieldFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Proper f] (ybar : GeometricPoint Y)
    (hfin : Finite (Points (fieldFiber f ybar.toFieldValuedPoint))) :
    ∃ (V : AlgebraicSpace S) (ι : V ⟶ Y) (hι : IsOpenImmersion ι),
      ybar.image ∈ Set.range (Points.map ι) ∧
        IsFinite (openInverseImageTo f ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
