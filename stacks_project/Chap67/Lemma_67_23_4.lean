/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Locality
import StacksCheckRecall

/-!
# Characterizations of local finite type for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

/- Lemma 67.23.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is locally of
finite type; `f` is of finite type at every point of `X`; every base change of
`f` along a morphism from a scheme is locally of finite type; every base change
of `f` along a morphism from an affine scheme is locally of finite type; there
is a surjective étale morphism from a scheme to `Y` along which the base
change of `f` is locally of finite type; there is a surjective étale morphism
`φ` from a scheme to `X` with `φ ≫ f` locally of finite type; every étale
scheme square over `f` has locally-of-finite-type top arrow; some étale scheme
square over `f` with surjective vertical source arrow has
locally-of-finite-type top arrow; and there are Zariski coverings of `Y` and of
the inverse images in `X` on which the pieces of `f` are locally of finite
type. -/
@[stacks 040Y] #check (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_tfae.{u, v} :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ LocallyOfFiniteType f
      , ∀ x : Points X, FiniteTypeAt f x
      , LocallyOfFiniteType.baseChangeOnSchemes f
      , LocallyOfFiniteType.baseChangeOnAffineSchemes f
      , LocallyOfFiniteType.existsSurjectiveEtaleTarget f
      , LocallyOfFiniteType.existsSurjectiveEtaleSource f
      , LocallyOfFiniteType.forallEtaleSquare f
      , LocallyOfFiniteType.existsEtaleSquare f
      , LocallyOfFiniteType.existsZariskiCover.{u, v} f ])
