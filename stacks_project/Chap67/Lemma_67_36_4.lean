module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic

/-!
# Characterizations of syntomicity for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.36.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is syntomic; `f`
is syntomic at every point of `X`; every base change of `f` along a morphism
from a scheme is syntomic; every base change of `f` along a morphism from an
affine scheme is syntomic; there is a surjective étale morphism from a scheme
to `Y` along which the base change of `f` is syntomic; there is a surjective
étale morphism `φ` from a scheme to `X` with `φ ≫ f` syntomic; every étale
scheme square over `f` has syntomic top arrow; some étale scheme square over
`f` with surjective vertical source arrow has syntomic top arrow; and there
are Zariski coverings of `Y` and of the inverse images in `X` on which the
pieces of `f` are syntomic. -/
@[stacks 03ZA]
theorem syntomic_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ Syntomic f
      , ∀ x : Points X, SyntomicAt f x
      , Syntomic.baseChangeOnSchemes f
      , Syntomic.baseChangeOnAffineSchemes f
      , Syntomic.existsSurjectiveEtaleTarget f
      , Syntomic.existsSurjectiveEtaleSource f
      , Syntomic.forallEtaleSquare f
      , Syntomic.existsEtaleSquare f
      , Syntomic.existsZariskiCover f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
