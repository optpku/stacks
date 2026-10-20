module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Homeomorph
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Homeomorphisms on points of algebraic stacks

The homeomorphism-on-points API is owned by the shared point-space module.
The historical closedness import preserves the comparison and point-cone API.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.isHomeomorphOnPoints :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    TopologicalSpace (Points X) → TopologicalSpace (Points Y) → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.isHomeomorphOnPoints_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y),
    isHomeomorphOnPoints τX τY f ↔
      @Continuous (Points X) (Points Y) τX τY (Points.map f) ∧
        @IsOpenMap (Points X) (Points Y) τX τY (Points.map f) ∧
          Function.Bijective (Points.map f))

#check (AlgebraicGeometry.AlgebraicStack.pointsIsHomeomorph :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.pointsIsHomeomorph_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    pointsIsHomeomorph f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isHomeomorphOnPoints τX τY f)

end AlgebraicGeometry.AlgebraicStack
