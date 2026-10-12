/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_39_2_Etale

/-!
# Characterizations of étaleness for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.39.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is étale;
`f` is étale at every point of `X`; every base change of `f` along a
morphism from a scheme is étale; every base change of `f` along a morphism
from an affine scheme is étale; there is a surjective étale morphism from
a scheme to `Y` along which the base change of `f` is étale; there is a
surjective étale morphism `φ` from a scheme to `X` with `φ ≫ f` étale;
every étale scheme square over `f` has étale top arrow; some étale scheme
square over `f` with surjective vertical source arrow has étale top arrow;
and there are Zariski coverings of `Y` and of the inverse images in `X` on
which the pieces of `f` are étale. -/
@[stacks 03XT]
theorem etale_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ Etale f
      , ∀ x : Points X, EtaleAt f x
      , Etale.baseChangeOnSchemes f
      , Etale.baseChangeOnAffineSchemes f
      , Etale.existsSurjectiveEtaleTarget f
      , Etale.existsSurjectiveEtaleSource f
      , Etale.forallEtaleSquare f
      , Etale.existsEtaleSquare f
      , Etale.existsZariskiCover f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
