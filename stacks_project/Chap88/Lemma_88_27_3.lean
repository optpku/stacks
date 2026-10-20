module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
import StacksCheckRecall

/-!
# Completion is an equivalence for affine locally Noetherian algebraic spaces

In the standing locally Noetherian setup of `completionFunctor` (88.27.0.1),
if `X` is affine then completing along `T` is an equivalence of categories.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

section

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
  [IsLocallyNoetherian X] [IsAffine X] (T : Closeds (Points X))

/- Lemma 88.27.3: for an affine locally Noetherian algebraic space `X`,
completion along `T` is an equivalence from locally finite-type morphisms
isomorphic over the complement of `T` to locally Noetherian rig-étale formal
algebraic spaces over the completion. This uses the stronger existing theorem
which does not require affineness. -/
@[stacks 0ARA] #check (AlgebraicGeometry.AlgebraicSpace.completionFunctor.instIsEquivalence X T :
  (AlgebraicGeometry.AlgebraicSpace.completionFunctor X T).IsEquivalence)

end
