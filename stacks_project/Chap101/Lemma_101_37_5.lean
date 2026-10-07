module

public import stacks_project.Chap101.Lemma_101_37_5_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.37.5 (1): if `f ≫ g` is universally closed and `g` is separated, then
`f` is universally closed. -/
@[stacks 0CPT] #check
  (UniversallyClosed.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [UniversallyClosed (f ≫ g)] [Separated g],
      UniversallyClosed f)

/- In particular, the image of `|X|` in `|Y|` is closed. -/
@[stacks 0CPT] #check
  (Closed.isClosed_range_points :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Closed f]
      {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)},
      IsPointsTopology X τX → IsPointsTopology Y τY →
        @IsClosed (Points Y) τY (Set.range (Points.map f)))

/- Lemma 101.37.5 (2): if `f ≫ g` is proper and `g` is separated, then `f` is
proper. -/
@[stacks 0CPT] #check
  (Proper.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [Proper (f ≫ g)] [Separated g],
      Proper f)
