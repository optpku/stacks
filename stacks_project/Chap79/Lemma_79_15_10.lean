/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting.SchemeLocalization
import StacksCheckRecall

/-!
# Quasi-splitting of a groupoid scheme after separated étale localization

In Situation 79.15.4, if the source and target are additionally flat and
locally of finite presentation, then there exists a separated étale scheme
neighborhood where the restriction of `R` is quasi-split over a
residue-field-preserving point lying over `u`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 79.15.10: In Situation 79.15.4 assume in addition that `s` and `t`
are flat and locally of finite presentation. Then there exists a scheme `U'`,
a separated étale morphism `U' ⟶ U`, and a point `u'` of `U'` lying over `u`
with `κ(u) = κ(u')` such that the restriction `R' = R|_{U'}` of `R` to `U'`
is quasi-split over `u'`. -/
@[stacks 04RY] #check (AlgebraicGeometry.GroupoidScheme.exists_separatedEtale_isQuasiSplitOver :
    ∀ {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left],
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      AlgebraicGeometry.IsSeparated g.left ∧
        AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
          IsIso (g.left.residueFieldMap u') ∧
            GroupoidAlgebraicSpace.IsQuasiSplitOver
              (GroupoidAlgebraicSpace.pullback
                (GroupoidAlgebraicSpace.ofScheme G)
                (objectRestrictionHom G (ofOverMap g)))
              (ofOver.pointsEquiv U' u'))

end AlgebraicGeometry.GroupoidScheme
