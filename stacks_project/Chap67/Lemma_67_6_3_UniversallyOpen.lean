module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Open and universally open morphisms of algebraic spaces

The canonical owner supplies openness on canonical point spaces and universal
openness. This module preserves the chapter import surface and the
explicit-topology characterization of openness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.pointsIsOpenMap_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    pointsIsOpenMap f ↔
      ∀ (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y)),
        IsPointsTopology X τX → IsPointsTopology Y τY →
          isOpenMapOnPoints τX τY f)

end AlgebraicGeometry.AlgebraicSpace
