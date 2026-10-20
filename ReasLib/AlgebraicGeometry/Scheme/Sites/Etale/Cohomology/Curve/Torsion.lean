/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Extension

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Scheme.Etale.CurveCohomology

/-- A locally torsion abelian étale sheaf on a separated finite-type scheme of dimension
at most one over an algebraically closed field satisfies vanishing above degree two,
affine and positive-characteristic primary vanishing above degree one, constructible
finiteness under prime-to-characteristic torsion or properness, invariance under extensions
of algebraically closed fields under prime-to-characteristic torsion or properness,
and surjectivity of degree-two restriction to every open subscheme. -/
theorem Properties.ofIsLocallyTorsion
    {k : Type u} [Field k] [IsAlgClosed k]
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
    (hF : IsLocallyTorsion F) :
    Properties X F := sorry

end AlgebraicGeometry.Scheme.Etale.CurveCohomology
