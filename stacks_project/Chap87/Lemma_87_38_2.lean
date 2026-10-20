module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace.BaseChange
import StacksCheckRecall

/-!
# Cartesianness of completion along a closed subspace

A morphism of algebraic spaces induces a cartesian square of completions along
a closed subspace and its inverse image, in the fppf functor-of-points
category. In particular the induced map of completions is representable by
algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits Opposite

noncomputable section

universe u

/- Lemma 87.38.2. Completion along a closed subspace and its inverse image
forms a cartesian square with the ambient morphism. The induced map of
completions is representable by algebraic spaces. -/
@[stacks 0GXV] #check
  (AlgebraicGeometry.AlgebraicSpace.completionAlongSubspace_isPullback :
    ∀ {S : Scheme.{u}} {X' X Z : AlgebraicSpace S}
      (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i],
      IsPullback (completionAlongSubspace.ι (inverseImageι f i))
        (completionAlongSubspace.map f i) f (completionAlongSubspace.ι i))

#check
  (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces_completionAlongSubspace_map :
    ∀ {S : Scheme.{u}} {X' X Z : AlgebraicSpace S}
      (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i],
      representableByAlgebraicSpaces (completionAlongSubspace.map f i))
