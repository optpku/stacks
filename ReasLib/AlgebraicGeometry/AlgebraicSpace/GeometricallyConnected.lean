module

public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber

/-!
# Morphisms with connected geometric fibres

A morphism of algebraic spaces has connected geometric fibres when the space of
points of every geometric fibre is connected.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces has connected geometric fibres if the space of
points of the fibre over every geometric point of the target is connected. -/
@[mk_iff]
class HasConnectedGeometricFibres {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The geometric fibre over every geometric point of the target is connected. -/
  connectedSpace_geometricFiber (ybar : GeometricPoint Y) :
    ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint))

namespace HasConnectedGeometricFibres

attribute [instance] HasConnectedGeometricFibres.connectedSpace_geometricFiber

/-- Connectedness of every geometric fibre is available from the property. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasConnectedGeometricFibres f] (ybar : GeometricPoint Y) :
    ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)) :=
  HasConnectedGeometricFibres.connectedSpace_geometricFiber ybar

/-- Connectedness of every geometric fibre witnesses that a morphism of algebraic
spaces has connected geometric fibres. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ ybar : GeometricPoint Y,
      ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint))) :
    HasConnectedGeometricFibres f :=
  sorry

/-- The identity morphism of an algebraic space has connected geometric fibres. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    HasConnectedGeometricFibres (𝟙 X) :=
  sorry

end HasConnectedGeometricFibres

end AlgebraicGeometry.AlgebraicSpace
