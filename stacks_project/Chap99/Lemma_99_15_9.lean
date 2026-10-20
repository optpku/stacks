module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.FormalObject
import StacksCheckRecall

/- Lemma 99.15.9: Every formal object of the stack of curves over Spec(ℤ)
is effective. -/
@[stacks 0D58] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.formalObject_isEffective :
    ∀ ξ : AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.FormalObject,
      AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.FormalObject.IsEffective ξ)
