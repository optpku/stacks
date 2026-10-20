/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
import StacksCheckRecall

/-!
# Characterizations of flatness for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.30.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is flat; `f` is
flat at every point of `X`; every base change of `f` along a morphism from a
scheme is flat; every base change of `f` along a morphism from an affine
scheme is flat; there is a surjective étale morphism from a scheme to `Y`
along which the base change of `f` is flat; there is a surjective étale
morphism `φ` from a scheme to `X` with `φ ≫ f` flat; every étale scheme
square over `f` has flat top arrow; some étale scheme square over `f` with
surjective vertical source arrow has flat top arrow; and there are Zariski
coverings of `Y` and of the inverse images in `X` on which the pieces of `f`
are flat. -/
@[stacks 03MM] #check (AlgebraicGeometry.AlgebraicSpace.flat_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ Flat f
      , ∀ x : Points X, FlatAt f x
      , Flat.baseChangeOnSchemes f
      , Flat.baseChangeOnAffineSchemes f
      , Flat.existsSurjectiveEtaleTarget f
      , Flat.existsSurjectiveEtaleSource f
      , Flat.forallEtaleSquare f
      , Flat.existsEtaleSquare f
      , Flat.existsZariskiCover.{u, v} f ])

end AlgebraicGeometry.AlgebraicSpace
