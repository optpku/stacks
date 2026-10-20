module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.Range
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.40.6 (1): if `f ≫ g` is universally closed and `g` is separated then
`f` is universally closed. -/
@[stacks 04NX] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [UniversallyClosed (f ≫ g)] [Separated g],
      UniversallyClosed f)

/- In particular, the image of `|X|` in `|Y|` is closed. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Closed.isClosed_range_points :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Closed f],
      IsClosed (Set.range (Points.map f)))

/- Lemma 67.40.6 (2): if `f ≫ g` is proper and `g` is separated then `f` is
proper. -/
@[stacks 04NX] #check
  (AlgebraicGeometry.AlgebraicSpace.Proper.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [Proper (f ≫ g)] [Separated g],
      Proper f)
