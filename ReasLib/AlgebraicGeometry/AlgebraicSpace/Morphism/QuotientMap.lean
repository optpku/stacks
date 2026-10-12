/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# Quotient maps on algebraic-space points
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The map on points of a morphism is a quotient map for the specified source
and target topologies. -/
def isQuotientMapOnPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @Topology.IsQuotientMap (Points X) (Points Y) τX τY (Points.map f)

/-- A morphism induces a quotient map on points for every pair of canonical
topologies on its source and target. -/
def pointsIsQuotientMap {S : Scheme.{u}} : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} f ↦
    ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
      IsPointsTopology X τX → IsPointsTopology Y τY → isQuotientMapOnPoints τX τY f

end AlgebraicGeometry.AlgebraicSpace
