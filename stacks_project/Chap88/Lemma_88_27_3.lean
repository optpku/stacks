module

public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap88.Lemma_88_27_2

/-!
# Completion is an equivalence for affine locally Noetherian algebraic spaces

In the standing locally Noetherian setup of `completionFunctor` (88.27.0.1),
if `X` is affine then completing along `T` is an equivalence of categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- If `X` is affine, the completion functor `functor X T` is essentially
surjective on locally Noetherian rig-étale morphisms over `X_/T`. -/
instance instEssSurj_functor {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] [IsAffine X] (T : Closeds (Points X)) :
    (functor X T).EssSurj :=
  sorry

/-- If `X` is affine, every object of `Target X T` lies in the essential image
of `functor X T`: a locally Noetherian rig-étale morphism `g : W ⟶ X_/T` is
isomorphic over `X_/T` to `f_/T` for some locally finite-type `f` that is an
isomorphism over the open complement of `T`. -/
theorem functor_essImage {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] [IsAffine X] (T : Closeds (Points X))
    (W : Target X T) :
    (functor X T).essImage W :=
  sorry

/-- Lemma 88.27.3: in the situation of `completionFunctor` (88.27.0.1), if `X`
is affine then the functor `functor X T` is an equivalence of categories. -/
@[stacks 0ARA]
instance instIsEquivalence_functor {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] [IsAffine X] (T : Closeds (Points X)) :
    (functor X T).IsEquivalence :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
