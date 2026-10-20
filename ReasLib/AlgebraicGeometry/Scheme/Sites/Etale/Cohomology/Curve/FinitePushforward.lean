/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FinitePushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.CurveCohomology

noncomputable section

universe u

/-- The eight étale cohomological properties of a locally torsion abelian sheaf on a
separated curve over an algebraically closed field are preserved by finite pushforward. -/
theorem AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofFinitePushforward
    {k : Type u} [Field k] [IsAlgClosed k]
    [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S),
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    (X Y : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [Scheme.Hom.FiniteType Y.hom]
    [IsSeparated X.hom] [IsSeparated Y.hom]
    [Fact (topologicalKrullDim X.left ≤ 1)] [Fact (topologicalKrullDim Y.left ≤ 1)]
    (f : X.left ⟶ Y.left) [IsFinite f]
    (h_over : f ≫ Y.hom = X.hom)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (h_torsion : IsLocallyTorsion F) (h_properties : Properties X F) :
    Properties Y ((etaleAbelianPushforward f).obj F) := sorry
