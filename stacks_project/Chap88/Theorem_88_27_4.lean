module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Equivalence
import StacksCheckRecall

/-!
# Completion is an equivalence on locally finite-type morphisms isomorphic over U

In the standing locally Noetherian setup of `completionFunctor` (88.27.0.1),
completing along a closed subset `T` is an equivalence of categories, without
an affineness hypothesis on `X`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Theorem 88.27.4: let `S` be a scheme, let `X` be a locally Noetherian
algebraic space over `S`, and let `T ⊂ |X|` be a closed subset, with
`U = openComplementAlong X T` the open subspace complementary to `T`. The
completion functor `completionFunctor X T` of 88.27.0.1, sending a locally
finite-type morphism `f : X' ⟶ X` that is an isomorphism over `U` to the
locally Noetherian rig-étale morphism `f_/T : X'_/T' ⟶ X_/T`, is an
equivalence of categories. -/
@[stacks 0ARB] #check (AlgebraicGeometry.AlgebraicSpace.completionFunctor.instIsEquivalence :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
    (T : Closeds (Points X)), (completionFunctor X T).IsEquivalence)
