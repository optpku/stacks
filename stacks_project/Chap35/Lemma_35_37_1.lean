module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.Affine
import StacksCheckRecall

universe u

/- Lemma 35.37.1: Every scheme descent datum over an fpqc covering whose component
structure morphisms are affine is effective. -/
@[stacks 0245] #check
  (AlgebraicGeometry.IsAffineHom.satisfiesDescentFpqc :
    CategoryTheory.MorphismProperty.SatisfiesDescent
      (@AlgebraicGeometry.IsAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) .fpqc)
