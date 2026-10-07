module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap76.Lemma_76_55_3_AtWorstNodal

/-!
# Characterizations of at-worst-nodal morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.55.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is at worst nodal
of relative dimension 1; every base change of `f` along a morphism from a
scheme is at worst nodal of relative dimension 1; every base change of `f`
along a morphism from an affine scheme is at worst nodal of relative
dimension 1; there is a surjective étale morphism from a scheme to `Y` along
which the base change of `f` is at worst nodal of relative dimension 1; there
is a surjective étale morphism `φ` from a scheme to `X` with `φ ≫ f` at worst
nodal of relative dimension 1; every étale scheme square over `f` has
at-worst-nodal top arrow; some étale scheme square over `f` with surjective
vertical source arrow has at-worst-nodal top arrow; and there are Zariski
coverings of `Y` and of the inverse images in `X` on which the pieces of `f`
are at worst nodal of relative dimension 1. -/
@[stacks 0DSG]
theorem atWorstNodal_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ AtWorstNodal f
      , AtWorstNodal.baseChangeOnSchemes f
      , AtWorstNodal.baseChangeOnAffineSchemes f
      , AtWorstNodal.existsSurjectiveEtaleTarget f
      , AtWorstNodal.existsSurjectiveEtaleSource f
      , AtWorstNodal.forallEtaleSquare f
      , AtWorstNodal.existsEtaleSquare f
      , AtWorstNodal.existsZariskiCover f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
