/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal.Locality
import StacksCheckRecall

/-!
# Characterizations of at-worst-nodal morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.55.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
#check (AlgebraicGeometry.AlgebraicSpace.atWorstNodal_tfae.{u, v} :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ AtWorstNodal f
      , AtWorstNodal.baseChangeOnSchemes f
      , AtWorstNodal.baseChangeOnAffineSchemes f
      , AtWorstNodal.existsSurjectiveEtaleTarget f
      , AtWorstNodal.existsSurjectiveEtaleSource f
      , etaleLocal
          (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) f
      , AtWorstNodal.existsEtaleSquare f
      , AtWorstNodal.existsZariskiCover.{u, v} f ])

end AlgebraicGeometry.AlgebraicSpace
