/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap79.Lemma_79_15_10

/-!
# Quasi-splitting after an affine étale scheme localization

In Situation 79.15.4, if the source and target are also flat and locally of
finite presentation and `U` is affine, the localization of Lemma 79.15.10 may
be taken to be an affine scheme étale over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 79.15.13: in Situation 79.15.4, if `s` and `t` are also flat and
locally of finite presentation and `U` is affine, then there exist an affine
scheme `U'` over `S`, an étale morphism `g : U' ⟶ U`, and a point `u'` of
`U'` lying over `u` with `IsIso (g.left.residueFieldMap u')` such that the
restriction `R' = R|_{U'}` of `R` to `U'` is quasi-split over `u'`. -/
@[stacks 04S0]
theorem exists_affineEtale_isQuasiSplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
        IsIso (g.left.residueFieldMap u') ∧
          GroupoidAlgebraicSpace.IsQuasiSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (ofOver.pointsEquiv U' u') :=
  sorry

/-- There exist an affine scheme `U'` over `S`, an étale morphism `U' ⟶ U`,
and a `Spec(κ(u))`-point of `U'` lying over `u` at which the restriction of
`R` is quasi-split. Equality of residue fields is encoded by the domain
`Spec(κ(u))`. -/
theorem exists_affineEtale_residueMap_isQuasiSplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U)
      (u' : ofOver (residueOver G u) ⟶ ofOver U'),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧
        u' ≫ ofOverMap g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsQuasiSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
