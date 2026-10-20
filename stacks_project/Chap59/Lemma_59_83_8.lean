/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Lemma_59_83_7
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.ReducedExtensionByZero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 59.83.8. On a reduced separated finite-type scheme of dimension at most
one over an algebraically closed field, extension by zero of constant prime cyclic
coefficients along any open immersion satisfies statements (1)–(8). -/
@[stacks 0A3Q] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofReducedExtensionByZeroConstantZMod :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
      [∀ {S T : Scheme.{u}} (f : T ⟶ S),
        ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom],
      topologicalKrullDim X.left ≤ 1 → ∀ [IsReduced X.left]
        (ell : ℕ) [Fact (Nat.Prime ell)]
        {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
        [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
          (etaleRestriction j).op.HasLeftKanExtension G],
      AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties X
        (AlgebraicGeometry.Etale.TorsionOnCurve.extensionByZeroConstantZMod j ell))
