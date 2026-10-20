/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.LocallyConstantExtensionByZero
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

universe u

/- Lemma 59.83.9. On a reduced separated finite-type scheme of dimension at most
one over an algebraically closed field, extension by zero from a connected open
subscheme of a finite locally constant sheaf of prime-field vector spaces satisfies
statements (1)–(8). -/
@[stacks 03SD] #check
  (AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties.ofReducedExtensionByZeroZModModule :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [∀ (Y : Scheme.{u}) (V : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
      [∀ {S T : Scheme.{u}} (f : T ⟶ S),
        ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
      (h_dim : topologicalKrullDim X.left ≤ 1) [IsReduced X.left]
      (ell : ℕ) [Fact (Nat.Prime ell)]
      {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] [ConnectedSpace U]
      [∀ H : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j).op.HasLeftKanExtension H]
      [U.smallEtaleTopology.HasSheafCompose
        (forget₂ (ModuleCat.{u} (ZMod ell)) AddCommGrpCat.{u})]
      [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} (ZMod ell))]
      [∀ V : U.Etale,
        HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} (ZMod ell))]
      (G : Sheaf U.smallEtaleTopology (ModuleCat.{u} (ZMod ell)))
      [IsLocallyConstantWith
        (fun M : ModuleCat.{u} (ZMod ell) ↦ Module.Finite (ZMod ell) M) G],
    AlgebraicGeometry.Scheme.Etale.CurveCohomology.Properties X
      (AlgebraicGeometry.Etale.TorsionOnCurve.extensionByZeroZModModule j G))
