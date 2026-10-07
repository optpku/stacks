module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_28_4_LocallyOfFinitePresentation

/-!
# Characterizations of local finite presentation for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.28.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is locally of
finite presentation; `f` is of finite presentation at every point of `X`;
every base change of `f` along a morphism from a scheme is locally of finite
presentation; every base change of `f` along a morphism from an affine scheme
is locally of finite presentation; there is a surjective étale morphism from a
scheme to `Y` along which the base change of `f` is locally of finite
presentation; there is a surjective étale morphism `φ` from a scheme to `X`
with `φ ≫ f` locally of finite presentation; every étale scheme square over
`f` has locally-of-finite-presentation top arrow; some étale scheme square
over `f` with surjective vertical source arrow has
locally-of-finite-presentation top arrow; and there are Zariski coverings of
`Y` and of the inverse images in `X` on which the pieces of `f` are locally of
finite presentation. -/
@[stacks 0410]
theorem locallyOfFinitePresentation_tfae {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ LocallyOfFinitePresentation f
      , ∀ x : Points X, FinitePresentationAt f x
      , LocallyOfFinitePresentation.baseChangeOnSchemes f
      , LocallyOfFinitePresentation.baseChangeOnAffineSchemes f
      , LocallyOfFinitePresentation.existsSurjectiveEtaleTarget f
      , LocallyOfFinitePresentation.existsSurjectiveEtaleSource f
      , LocallyOfFinitePresentation.forallEtaleSquare f
      , LocallyOfFinitePresentation.existsEtaleSquare f
      , LocallyOfFinitePresentation.existsZariskiCover f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
