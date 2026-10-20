module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stack
import StacksCheckRecall

/-!
# Lemma 99.15.3

The category Curves of families of curves is a stack in groupoids over
`Sch_fppf`.
-/

universe u

/- Lemma 99.15.3: the category of families of curves is a stack in groupoids
over the fppf site. -/
@[stacks 0D52] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsStackInGroupoids :
    ∀ S : AlgebraicGeometry.Scheme.{u},
      CategoryTheory.IsStack.InGroupoids
        (AlgebraicGeometry.Scheme.fppfTopology.over S)
        (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p S))
