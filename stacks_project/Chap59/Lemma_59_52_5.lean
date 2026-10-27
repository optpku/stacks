/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Lemma_59_52_5_HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.ComplexSystem
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf
open ComplexShape

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
variable [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I,
    HasDerivedCategory (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I,
    HasDerivedCategory (Sheaf (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).Additive]
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
variable [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasDerivedCategory (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
    cS.pt.smallEtaleTopology cX.pt.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
        cS.pt.smallEtaleTopology cX.pt.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [∀ i : I, Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
        (DS.obj (OrderDual.toDual i)).smallEtaleTopology
        (DX.obj (OrderDual.toDual i)).smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable (F : AbelianSheafComplexSystem DX) (a p : ℤ)
variable (hcX : IsLimit cX) (hcS : IsLimit cS)
variable (hF : ∀ i, (F.obj i).IsStrictlyGE a)
variable [HasColimit (AbelianSheafComplexSystem.inverseImageComplexDiagram (D := DX) cX F)]
variable [HasColimit
    (HigherDirectImage.ComplexSystem.diagram DX DS g hg cS F p)]

/- Lemma 59.52.5: a compatible uniformly bounded-below system of complexes of abelian étale
sheaves has higher direct images commuting with the filtered colimit in every degree. -/
@[stacks 0GIV] #check
  (AlgebraicGeometry.Scheme.Etale.HigherDirectImage.ComplexSystem.isIso_comparison DX DS g hg cX cS gX hgX F p hcX hcS hF :
      IsIso (HigherDirectImage.ComplexSystem.comparison DX DS g hg cX cS gX hgX F p))

end AlgebraicGeometry.Scheme.Etale

end
