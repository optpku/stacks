module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
import StacksCheckRecall

@[expose] public section

/-! # Squares indexing an algebraic-space f-map

This is the square-indexing part of Definition 66.18.9 (03G3). The f-map family and its
restriction compatibility are owned separately; the geometric square data live in ReasLib.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 66.18.9: the components of an `f`-map are indexed by commutative squares of
étale scheme charts over the morphism `f` of algebraic spaces. -/
@[stacks 03G3] #check (AlgebraicGeometry.AlgebraicSpace.EtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Type (u + 1))
