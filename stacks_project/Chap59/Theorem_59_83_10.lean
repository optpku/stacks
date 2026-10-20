/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Torsion
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.CurveCohomology

universe u

/- Theorem 59.83.10. Locally torsion abelian étale sheaves on separated finite-type
schemes of dimension at most one over an algebraically closed field satisfy the eight
vanishing, finiteness, base-change, and open-restriction properties. -/
@[stacks 03SC] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofIsLocallyTorsion :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S),
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F),
      Properties X F)
