/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Characterizations of smoothness for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.37.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is smooth; `f` is
smooth at every point of `X`; every base change of `f` along a morphism from a
scheme is smooth; every base change of `f` along a morphism from an affine
scheme is smooth; there is a surjective étale morphism from a scheme to `Y`
along which the base change of `f` is smooth; there is a surjective étale
morphism `φ` from a scheme to `X` with `φ ≫ f` smooth; every étale scheme
square over `f` has smooth top arrow; some étale scheme square over `f` with
surjective vertical source arrow has smooth top arrow; and there are Zariski
coverings of `Y` and of the inverse images in `X` on which the pieces of `f`
are smooth. -/
@[stacks 03ZF]
theorem smooth_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ Smooth f
      , ∀ x : Points X, SmoothAt f x
      , Smooth.baseChangeOnSchemes f
      , Smooth.baseChangeOnAffineSchemes f
      , Smooth.existsSurjectiveEtaleTarget f
      , Smooth.existsSurjectiveEtaleSource f
      , Smooth.forallEtaleSquare f
      , Smooth.existsEtaleSquare f
      , Smooth.existsZariskiCover f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
