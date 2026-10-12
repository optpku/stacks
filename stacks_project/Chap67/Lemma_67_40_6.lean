/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_40_6_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.40.6 (1): if `f ≫ g` is universally closed and `g` is separated then
`f` is universally closed. -/
@[stacks 04NX] #check
  (UniversallyClosed.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [UniversallyClosed (f ≫ g)] [Separated g],
      UniversallyClosed f)

/- In particular, the image of `|X|` in `|Y|` is closed. -/
#check
  (Closed.isClosed_range_points :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Closed f]
      {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)},
      IsPointsTopology X τX → IsPointsTopology Y τY →
        @IsClosed (Points Y) τY (Set.range (Points.map f)))

/- Lemma 67.40.6 (2): if `f ≫ g` is proper and `g` is separated then `f` is
proper. -/
@[stacks 04NX] #check
  (Proper.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [Proper (f ≫ g)] [Separated g],
      Proper f)
