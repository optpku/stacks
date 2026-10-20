/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (DX DS : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap DX hij)]
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
variable [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I,
    HasInjectiveResolutions
      (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable (g : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
variable (hg : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DX hij ≫ g i =
      g j ≫ OrderDualInverseSystem.transitionMap DS hij)
variable [∀ i : I, QuasiCompact (g i)]
variable [∀ i : I, QuasiSeparated (g i)]
variable (cX : Cone DX) (cS : Cone DS)
variable (gX : cX.pt ⟶ cS.pt)
variable (hgX : ∀ i : I,
    cX.π.app (OrderDual.toDual i) ≫ g i = gX ≫ cS.π.app (OrderDual.toDual i))
variable [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u}) (p : ℕ)
variable [HasColimit (inverseImageDiagram DX cX (abelianPushforwardSystem DX cX F))]
variable [HasColimit
  (higherDirectImage_pullbackDiagram DX DS g hg cS
    (abelianPushforwardSystem DX cX F) p)]
/- Lemma 59.51.10: for a directed inverse system of quasi-compact quasi-separated
morphisms `g_i : X_i ⟶ S_i` with affine transition morphisms on both `X` and `S`,
writing `g : X ⟶ S` for the limit morphism with projections `f_i` and `h_i`, and
letting `F` be an abelian sheaf on `X.Etale`, the comparison
`colim_i h_i⁻¹ R^p g_{i*}(f_{i*} F) ⟶ R^p g_* F` of sheaves on `S.Etale` is an
isomorphism for every `p ≥ 0`. -/
@[stacks 0DV2] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImage_eq_colimit_stagePushforward DX DS g hg cX cS gX hgX F p :
    ∀ (hcX : IsLimit cX) (hcS : IsLimit cS),
      IsIso (higherDirectImage_stagePushforwardComparison DX DS g hg cX cS gX hgX F p))

end AlgebraicGeometry.Scheme.Etale

end
