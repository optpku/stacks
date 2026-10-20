module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Lemma 99.15.2: the category of families of curves is fibred in groupoids. -/
@[stacks 0D51] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsFiberedInGroupoids :
    ∀ S : Scheme.{u}, Functor.IsFibered.InGroupoids
      (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.p S))
