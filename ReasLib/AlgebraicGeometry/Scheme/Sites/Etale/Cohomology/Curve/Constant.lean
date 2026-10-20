/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Extension
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.ZMod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.CurveCohomology

noncomputable section

universe u

/-- On a smooth separated finite-type scheme of dimension at most one over an
algebraically closed field, constant coefficients modulo any prime satisfy the
eight étale cohomological vanishing, finiteness, base-change, and open-restriction
properties. -/
theorem AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofSmoothConstantZMod
    {k : Type u} [Field k] [IsAlgClosed k]
    [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S),
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (h_dim : topologicalKrullDim X.left ≤ 1) [Smooth X.hom]
    (ell : ℕ) [Fact (Nat.Prime ell)] :
    Properties X (CategoryTheory.constantZModSheaf.{_, _, u} X.left.smallEtaleTopology ell) := sorry
