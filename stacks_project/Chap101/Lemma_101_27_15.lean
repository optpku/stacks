module

public import stacks_project.Chap101.Lemma_101_27_15_OpenMap
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Flat locally of finite presentation morphisms of algebraic stacks are open on points

A morphism of algebraic stacks that is flat and locally of finite presentation
induces an open map on underlying point spaces.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.27.15: Let `f : X ⟶ Y` be a morphism of algebraic stacks that is
flat and locally of finite presentation. Then `|f| : |X| ⟶ |Y|` is open, i.e.
`Points.map f : Points X → Points Y` is an open map for every pair of canonical
topologies. -/
@[stacks 06R7]
theorem Flat.pointsIsOpenMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] : pointsIsOpenMap f :=
  sorry

/-- A flat locally of finite presentation morphism of algebraic stacks induces an
open map on points for any pair of canonical topologies. -/
theorem Flat.isOpenMapOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isOpenMapOnPoints τX τY f :=
  sorry

/-- The image of an open set of points under a flat locally of finite
presentation morphism of algebraic stacks is open. -/
theorem Flat.isOpen_image {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY)
    {U : Set (Points X)} (hU : @IsOpen (Points X) τX U) :
    @IsOpen (Points Y) τY (Points.map f '' U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
