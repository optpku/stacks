module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Reduction
import StacksCheckRecall

/-!
# Reduction of the completion along a closed subset

The reduction of the formal completion of an algebraic space along a closed
subset is the reduced induced closed subspace corresponding to that subset.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory TopologicalSpace

universe u

/- Lemma 87.14.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `T ⊆ Points X` be a closed subset. The reduction of the completion
`completionAlong X T` of `X` along `T` is the reduced induced closed subspace
of `X` corresponding to `T`. -/
@[stacks 0GB9] #check (AlgebraicGeometry.AlgebraicSpace.reduction_completionAlong :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)),
    (SpacePresheaf.reduction (completionAlong X T)).image (completionAlong.ι X T) =
      Subfunctor.range (ClosedSubspaceStructure.reduced T).ι)
