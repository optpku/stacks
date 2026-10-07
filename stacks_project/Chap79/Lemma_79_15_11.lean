module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap79.Lemma_79_15_8

/-!
# Strong splitting after an affine étale scheme localization

In Situation 79.15.2, if the source and target are also flat and locally of
finite presentation and `U` is affine, the localization of Lemma 79.15.8 may
be taken to be an affine scheme étale over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 79.15.11: in Situation 79.15.2, if `s` and `t` are also flat and
locally of finite presentation and `U` is affine, then there exist an affine
scheme `U'` over `S`, an étale morphism `g : U' ⟶ U`, and a point `u'` of
`U'` lying over `u` with `IsIso (g.left.residueFieldMap u')` such that the
restriction `R' = R|_{U'}` of `R` to `U'` is strongly split over `u'`. -/
@[stacks 04RZ]
theorem exists_affineEtale_isStronglySplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
        IsIso (g.left.residueFieldMap u') ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (ofOver.pointsEquiv U' u') :=
  sorry

/-- There exist an affine scheme `U'` over `S`, an étale morphism `U' ⟶ U`,
and a `Spec(κ(u))`-point of `U'` lying over `u` at which the restriction of
`R` is strongly split. Equality of residue fields is encoded by the domain
`Spec(κ(u))`. -/
theorem exists_affineEtale_residueMap_isStronglySplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U)
      (u' : ofOver (residueOver G u) ⟶ ofOver U'),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧
        u' ≫ ofOverMap g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
