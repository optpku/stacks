module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Smooth
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.18.5: the Nagata property for schemes is local for the smooth precoverage. -/
@[stacks 036E] #check
  (AlgebraicGeometry.Scheme.Nagata.smoothLocal :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.Scheme.Nagata :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage)
