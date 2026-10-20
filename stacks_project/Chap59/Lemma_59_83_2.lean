/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Lemma_59_83_4_Statements
public import stacks_project.Chap59.Theorem_59_82_7_Gabber_Restrict
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Constant
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

/-- The constant sheaf of abelian groups on `X.smallEtaleTopology` with value
`ULift.{u} (ZMod ell)`. -/
public noncomputable abbrev constantZModSheaf (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] (ell : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  CategoryTheory.constantZModSheaf.{_, _, u} X.smallEtaleTopology ell

end AlgebraicGeometry.Etale.TorsionOnCurve

/- Lemma 59.83.2. On a smooth separated finite-type scheme of dimension at most
one over an algebraically closed field, constant prime cyclic coefficients
satisfy statements (1)–(8). -/
@[stacks 0A5B] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofSmoothConstantZMod :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
      [∀ {S T : Scheme.{u}} (f : T ⟶ S),
        ((Scheme.smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom],
      topologicalKrullDim X.left ≤ 1 → ∀ [Smooth X.hom]
        (ell : ℕ) [Fact (Nat.Prime ell)],
      AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties X
        (CategoryTheory.constantZModSheaf.{_, _, u} X.left.smallEtaleTopology ell))
