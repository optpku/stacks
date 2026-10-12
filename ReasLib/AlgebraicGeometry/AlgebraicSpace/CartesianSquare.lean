/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The square of algebraic spaces over `S` with horizontal maps `q` and `f`
and vertical maps `p` and `g` is cartesian. -/
def IsCartesianSquare {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
    (p : W ⟶ X) (q : W ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ Y) : Prop :=
  CategoryTheory.IsPullback q p g f

end AlgebraicGeometry.AlgebraicSpace
