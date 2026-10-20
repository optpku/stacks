module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.Reduction
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Remark 68.14.3: We will see in Limits of Spaces, Lemma 70.15.3 that an
algebraic space whose reduction is a scheme is a scheme. -/
@[stacks 049D] #check (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_reduction :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsScheme (AlgebraicGeometry.AlgebraicSpace.reduction X)],
    AlgebraicGeometry.AlgebraicSpace.IsScheme X)
