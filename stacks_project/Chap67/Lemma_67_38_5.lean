/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Local
import StacksCheckRecall

/-!
# Characterizations of unramifiedness for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.38.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is unramified;
`f` is unramified at every point of `X`; every base change of `f` along a
morphism from a scheme is unramified; every base change of `f` along a morphism
from an affine scheme is unramified; there is a surjective étale morphism from
a scheme to `Y` along which the base change of `f` is unramified; there is a
surjective étale morphism `φ` from a scheme to `X` with `φ ≫ f` unramified;
every étale scheme square over `f` has unramified top arrow; some étale scheme
square over `f` with surjective vertical source arrow has unramified top arrow;
and there are Zariski coverings of `Y` and of the inverse images in `X` on
which the pieces of `f` are unramified. -/
@[stacks 03ZK] #check (AlgebraicGeometry.AlgebraicSpace.unramified_tfae.{u, v} :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ Unramified f
      , ∀ x : Points X, UnramifiedAt f x
      , Unramified.baseChangeOnSchemes f
      , Unramified.baseChangeOnAffineSchemes f
      , Unramified.existsSurjectiveEtaleTarget f
      , Unramified.existsSurjectiveEtaleSource f
      , Unramified.forallEtaleSquare f
      , Unramified.existsEtaleSquare f
      , Unramified.existsZariskiCover.{u, v} f ])

end AlgebraicGeometry.AlgebraicSpace
