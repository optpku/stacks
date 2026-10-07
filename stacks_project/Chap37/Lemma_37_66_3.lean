module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.66.3: The property of being an ind-quasi-affine morphism is stable under
composition. -/
@[stacks 0F1V] #check
  (AlgebraicGeometry.IndQuasiAffineHom.stableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.IndQuasiAffineHom :
        MorphismProperty AlgebraicGeometry.Scheme.{u}))
