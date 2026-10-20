/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyClosed.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.37.5 (1): if `f ≫ g` is universally closed and `g` is separated, then
`f` is universally closed. -/
@[stacks 0CPT] #check
  (AlgebraicGeometry.AlgebraicStack.UniversallyClosed.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [UniversallyClosed (f ≫ g)] [Separated g],
      UniversallyClosed f)

/- In particular, the image of `|X|` in `|Y|` is closed. -/
#check
  (AlgebraicGeometry.AlgebraicStack.Closed.isClosed_range_points :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Closed f]
      {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)},
      IsPointsTopology X τX → IsPointsTopology Y τY →
        @IsClosed (Points Y) τY (Set.range (Points.map f)))

/- Lemma 101.37.5 (2): if `f ≫ g` is proper and `g` is separated, then `f` is
proper. -/
@[stacks 0CPT] #check
  (AlgebraicGeometry.AlgebraicStack.Proper.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [Proper (f ≫ g)] [Separated g],
      Proper f)
