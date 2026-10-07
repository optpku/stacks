module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty.IndQuasiAffine
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 40.15.3 (Gabber): every scheme descent datum over an fpqc covering whose
component structure morphisms are ind-quasi-affine is effective. -/
@[stacks 0APK] #check
  (AlgebraicGeometry.IndQuasiAffineHom.satisfiesDescentFpqc :
    CategoryTheory.MorphismProperty.SatisfiesDescent
      (@AlgebraicGeometry.IndQuasiAffineHom :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) .fpqc)
