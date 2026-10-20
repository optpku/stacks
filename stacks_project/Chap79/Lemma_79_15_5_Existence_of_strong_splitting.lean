/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.StrongSplitting.EtaleLocalization

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

universe u

/- Lemma 79.15.5 (Existence of strong splitting)
There is an étale algebraic-space localization with a residue-field point over the
original point at which the restricted groupoid is strongly split. -/
@[stacks 03FM] #check (AlgebraicGeometry.GroupoidScheme.exists_etale_isStronglySplitOver :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [GroupoidScheme.StrongSplitting G u],
    ∃ (U' : AlgebraicSpace S) (g : U' ⟶ ofOver G.U)
      (u' : ofOver (GroupoidScheme.residueOver G u) ⟶ U'),
      AlgebraicSpace.Etale g ∧
        u' ≫ g = GroupoidScheme.residueMap G u ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (GroupoidScheme.objectRestrictionHom G g))
            (GroupoidScheme.residueFieldPoint G u u'))

#check (AlgebraicGeometry.GroupoidScheme.isStronglySplitOver_finitePart :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [GroupoidScheme.StrongSplitting G u],
    GroupoidAlgebraicSpace.IsStronglySplitOver
      (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
        (GroupoidAlgebraicSpace.finitePartHom (GroupoidAlgebraicSpace.ofScheme G)).obj)
      (GroupoidScheme.strongSplittingResiduePoint G u))
