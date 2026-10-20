module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Separation
import StacksCheckRecall

/-!
# Separatedness along the completion functor

Under the standing hypotheses of Theorem 88.27.4, a locally finite-type
morphism isomorphic over the complementary open is separated if and only if
the corresponding morphism of completions is separated and its relative
diagonal is rig-surjective.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace

universe u

/- Lemma 88.28.3: with the standing hypotheses of Theorem 88.27.4, if
`f : X' ⟶ X` corresponds to `g : W ⟶ X_/T` under `completionFunctor X T`,
then `AlgebraicSpace.Separated f` if and only if
`FormalAlgebraicSpace.Separated g` and the relative diagonal
`pullback.diagonal g : W ⟶ W ×_{X_/T} W` is
`FormalAlgebraicSpace.RigSurjective`. The corresponding morphism is the
canonical `completionAlong.map f T`. -/
@[stacks 0ARW] #check (AlgebraicGeometry.AlgebraicSpace.completionFunctor.separated_hom_iff :
    ∀ {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))],
    AlgebraicSpace.Separated f ↔
      FormalAlgebraicSpace.Separated (completionAlong.map f T) ∧
        FormalAlgebraicSpace.RigSurjective
          (pullback.diagonal (completionAlong.map f T)))
