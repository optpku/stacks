/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_37_1_Proper

/-!
# Cancellation of universal closedness and properness against separated postcomposition

If a composite morphism of algebraic stacks is universally closed (resp. proper)
and the second factor is separated, then the first factor is universally closed
(resp. proper). A closed morphism has closed image on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyClosed

/-- If a composite morphism of algebraic stacks is universally closed and the
second factor is separated, then the first factor is universally closed. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed (f ≫ g)] [Separated g] : UniversallyClosed f :=
  sorry

end UniversallyClosed

namespace Closed

/-- A closed morphism of algebraic stacks has closed image of points, for any
pair of canonical topologies on the source and target. -/
theorem isClosed_range_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Closed f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    @IsClosed (Points Y) τY (Set.range (Points.map f)) :=
  sorry

end Closed

namespace Proper

/-- If a composite morphism of algebraic stacks is proper and the second factor
is separated, then the first factor is proper. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [Proper (f ≫ g)] [Separated g] : Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicStack
