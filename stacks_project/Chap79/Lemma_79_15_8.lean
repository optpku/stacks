/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.StrongSplitting.SchemeLocalization
import StacksCheckRecall

/-! # Strong splitting after a separated étale scheme localization -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 79.15.8: in Situation 79.15.2, if `s` and `t` are also flat and
locally of finite presentation, then there exist a scheme `U'` over `S`, a
separated étale morphism `g : U' ⟶ U`, and a point `u'` of `U'` lying over
`u` with `IsIso (g.left.residueFieldMap u')` such that the restriction of `R`
to `U'` is strongly split over `u'`. The space `U'` may be taken to be
`(finitePart (ofScheme G)).U.left`, the map `g` to be `finitePartToU`, and
the point `u'` to arise from `strongSplittingHom`. -/
@[stacks 04RX] #check (AlgebraicGeometry.GroupoidScheme.exists_separatedEtale_scheme_isStronglySplitOver :
  ∀ {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left],
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      IsSeparated g.left ∧ AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
        IsIso (g.left.residueFieldMap u') ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (ofOver.pointsEquiv U' u'))

#check (AlgebraicGeometry.GroupoidScheme.exists_separatedEtale_residueMap_isStronglySplitOver :
  ∀ {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left],
    ∃ (U' : Over S) (g : U' ⟶ G.U)
      (u' : ofOver (residueOver G u) ⟶ ofOver U'),
      IsSeparated g.left ∧ AlgebraicGeometry.Etale g.left ∧
        u' ≫ ofOverMap g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (residueFieldPoint G u u'))

end AlgebraicGeometry.GroupoidScheme
