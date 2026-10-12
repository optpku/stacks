/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite

/-!
# Characterizations of local quasi-finiteness for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.27.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is locally
quasi-finite; `f` is quasi-finite at every point of `X`; every base change of
`f` along a morphism from a scheme is locally quasi-finite; every base change
of `f` along a morphism from an affine scheme is locally quasi-finite; there
is a surjective étale morphism from a scheme to `Y` along which the base
change of `f` is locally quasi-finite; there is a surjective étale morphism
`φ` from a scheme to `X` with `φ ≫ f` locally quasi-finite; every étale
scheme square over `f` has locally quasi-finite top arrow; some étale scheme
square over `f` with surjective vertical source arrow has locally
quasi-finite top arrow; and there are Zariski coverings of `Y` and of the
inverse images in `X` on which the pieces of `f` are locally quasi-finite. -/
@[stacks 040Z]
theorem locallyQuasiFinite_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    List.TFAE
      [ LocallyQuasiFinite f
      , ∀ x : Points X, QuasiFiniteAt f x
      , LocallyQuasiFinite.baseChangeOnSchemes f
      , LocallyQuasiFinite.baseChangeOnAffineSchemes f
      , LocallyQuasiFinite.existsSurjectiveEtaleTarget f
      , LocallyQuasiFinite.existsSurjectiveEtaleSource f
      , LocallyQuasiFinite.forallEtaleSquare f
      , LocallyQuasiFinite.existsEtaleSquare f
      , LocallyQuasiFinite.existsZariskiCover f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
