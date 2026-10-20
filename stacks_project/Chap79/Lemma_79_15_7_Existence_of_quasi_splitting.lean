/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.QuasiSplitting.EtaleLocalization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 79.15.7 (Existence of quasi-splitting)
There is an étale algebraic-space neighborhood with a residue-field-valued lift
at which the restricted groupoid is quasi-split. -/
@[stacks 04RW] #check (AlgebraicGeometry.GroupoidScheme.exists_etale_isQuasiSplitOver :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsQuasiSplittingSituation G u],
    ∃ (U' : AlgebraicSpace S) (g : U' ⟶ ofOver G.U)
      (u' : ofOver (residueOver G u) ⟶ U'),
      AlgebraicSpace.Etale g ∧
        u' ≫ g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsQuasiSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G g))
            (residueFieldPoint G u u'))

#check (AlgebraicGeometry.GroupoidScheme.isQuasiSplitOver_finitePart :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsQuasiSplittingSituation G u],
    GroupoidAlgebraicSpace.IsQuasiSplitOver
      (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
        (GroupoidAlgebraicSpace.finitePartHom
          (GroupoidAlgebraicSpace.ofScheme G)).obj)
      (quasiSplittingResiduePoint G u))

end AlgebraicGeometry.GroupoidScheme
