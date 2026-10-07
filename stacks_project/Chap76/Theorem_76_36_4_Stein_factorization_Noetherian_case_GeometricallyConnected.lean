module

public import Mathlib.Topology.Connected.Basic
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_18_6_Fibre

/-!
# Morphisms of algebraic spaces with connected geometric fibres

A morphism of algebraic spaces has connected geometric fibres when the space of
points of every geometric fibre is connected.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- A morphism of algebraic spaces has connected geometric fibres if the space of
points of the fibre over every geometric point of the target is connected. -/
@[mk_iff]
class HasConnectedGeometricFibres {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- The geometric fibre over every geometric point of the target is connected. -/
  connectedSpace_geometricFiber (ybar : GeometricPoint Y) :
    ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint))

namespace HasConnectedGeometricFibres

/-- A morphism with connected geometric fibres has connected space of points on
every geometric fibre. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasConnectedGeometricFibres f] (ybar : GeometricPoint Y) :
    ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint)) :=
  sorry

/-- Connectedness of every geometric fibre witnesses that a morphism of algebraic
spaces has connected geometric fibres. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ ybar : GeometricPoint Y,
      ConnectedSpace (Points (fieldFiber f ybar.toFieldValuedPoint))) :
    HasConnectedGeometricFibres f :=
  sorry

end HasConnectedGeometricFibres

/-- The identity morphism of an algebraic space has connected geometric fibres. -/
instance instHasConnectedGeometricFibres_id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    HasConnectedGeometricFibres (𝟙 X) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
