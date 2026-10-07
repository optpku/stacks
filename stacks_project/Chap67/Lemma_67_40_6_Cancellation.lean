module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Cancellation of universal closedness and properness against separated postcomposition

If a composite morphism of algebraic spaces is universally closed (resp. proper)
and the second factor is separated, then the first factor is universally closed
(resp. proper). A closed morphism has closed image on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/-- If a composite morphism of algebraic spaces is universally closed and the
second factor is separated, then the first factor is universally closed. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed (f ≫ g)] [Separated g] : UniversallyClosed f := sorry

end UniversallyClosed

namespace Closed

/-- A closed morphism of algebraic spaces has closed image of points, for any
pair of canonical topologies on the source and target. -/
theorem isClosed_range_points {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Closed f] {τX : TopologicalSpace (Points X)}
    {τY : TopologicalSpace (Points Y)} (hX : IsPointsTopology X τX)
    (hY : IsPointsTopology Y τY) :
    @IsClosed (Points Y) τY (Set.range (Points.map f)) := sorry

end Closed

namespace Proper

/-- If a composite morphism of algebraic spaces is proper and the second factor
is separated, then the first factor is proper. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Proper (f ≫ g)] [Separated g] : Proper f := sorry

end Proper

/-- Universally closed morphisms of algebraic spaces cancel against a separated
postcomposition. -/
instance universallyClosed_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@UniversallyClosed S : MorphismProperty (AlgebraicSpace S))
      (@Separated S) := sorry

/-- Proper morphisms of algebraic spaces cancel against a separated
postcomposition. -/
instance proper_hasOfPostcompProperty {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@Proper S : MorphismProperty (AlgebraicSpace S))
      (@Separated S) := sorry

end AlgebraicGeometry.AlgebraicSpace
