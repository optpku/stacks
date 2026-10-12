/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap88.«88_27_0_1»

/-!
# Completion is an equivalence on locally finite-type morphisms isomorphic over U

In the standing locally Noetherian setup of `completionFunctor` (88.27.0.1),
completing along a closed subset `T` is an equivalence of categories, without
an affineness hypothesis on `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Theorem 88.27.4: let `S` be a scheme, let `X` be a locally Noetherian
algebraic space over `S`, and let `T ⊂ |X|` be a closed subset, with
`U = openComplementAlong X T` the open subspace complementary to `T`. The
completion functor `completionFunctor X T` of 88.27.0.1, sending a locally
finite-type morphism `f : X' ⟶ X` that is an isomorphism over `U` to the
locally Noetherian rig-étale morphism `f_/T : X'_/T' ⟶ X_/T`, is an
equivalence of categories. -/
@[stacks 0ARB]
instance completionFunctor.instIsEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    (completionFunctor X T).IsEquivalence :=
  sorry

/-- Every object of `completionAlong.Target X T` lies in the essential image of
`completionFunctor X T`: a locally Noetherian rig-étale morphism `g : W ⟶ X_/T`
is isomorphic over `X_/T` to `f_/T` for some locally finite-type `f` that is an
isomorphism over `U = openComplementAlong X T`. -/
theorem completionFunctor.essImage {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X))
    (W : completionAlong.Target X T) :
    (completionFunctor X T).essImage W :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
