module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting.AffineLocalization
import StacksCheckRecall

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

/- Lemma 79.15.13: in Situation 79.15.4, if `s` and `t` are also flat and
locally of finite presentation and `U` is affine, then there exist an affine
scheme `U'` over `S`, an étale morphism `g : U' ⟶ U`, and a point `u'` of
`U'` lying over `u` with `IsIso (g.left.residueFieldMap u')` such that the
restriction `R' = R|_{U'}` of `R` to `U'` is quasi-split over `u'`. -/
@[stacks 04S0] #check (AlgebraicGeometry.GroupoidScheme.exists_affineEtale_isQuasiSplitOver :
  ∀ {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left],
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
        IsIso (g.left.residueFieldMap u') ∧
          GroupoidAlgebraicSpace.IsQuasiSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (ofOver.pointsEquiv U' u'))

#check (AlgebraicGeometry.GroupoidScheme.exists_affineEtale_residueMap_isQuasiSplitOver :
  ∀ {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [IsAffine G.U.left]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left],
    ∃ (U' : Over S) (g : U' ⟶ G.U)
      (u' : ofOver (residueOver G u) ⟶ ofOver U'),
      IsAffine U'.left ∧ AlgebraicGeometry.Etale g.left ∧
        u' ≫ ofOverMap g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsQuasiSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (residueFieldPoint G u u'))

end AlgebraicGeometry.GroupoidScheme
