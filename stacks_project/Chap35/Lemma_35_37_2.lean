/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.ClosedImmersion
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.37.2: Every scheme descent datum over an fpqc covering whose component
structure morphisms are closed immersions is effective. -/
@[stacks 03I0]
#check
  (AlgebraicGeometry.IsClosedImmersion.satisfiesDescentFpqc :
    CategoryTheory.MorphismProperty.SatisfiesDescent
      (@AlgebraicGeometry.IsClosedImmersion :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) .fpqc)
