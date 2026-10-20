/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.NormalizedInverseSystem
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.51.8: higher direct images commute with directed inverse limits
of quasi-compact quasi-separated scheme morphisms with affine transitions. -/
@[stacks 0EYM] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImage_colimit_inverseSystemOfMorphisms :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (DX DS : OrderDual I ⥤ Scheme.{u})
      [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
      [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
      [∀ i : I, HasInjectiveResolutions
        (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
      [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
      [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
      [∀ {T U : Scheme.{u}} (morphism : U ⟶ T) (sheaf : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
        (smallEtalePullback morphism).op.HasLeftKanExtension sheaf]
      [∀ {T U : Scheme.{u}} (morphism : U ⟶ T),
        ((smallEtalePullback morphism).sheafPushforwardContinuous AddCommGrpCat.{u}
          T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
      (g : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
      (hg : ∀ {i j : I} (hij : i ≤ j),
        OrderDualInverseSystem.transitionMap DX hij ≫ g i =
          g j ≫ OrderDualInverseSystem.transitionMap DS hij)
      (cX : Cone DX) (cS : Cone DS) (gX : cX.pt ⟶ cS.pt)
      (hgX : ∀ i : I,
        cX.π.app (OrderDual.toDual i) ≫ g i = gX ≫ cS.π.app (OrderDual.toDual i))
      [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
      [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
      [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
      [HasInjectiveResolutions (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
      (F : AlgebraicGeometry.Scheme.Etale.AbelianSheafSystem DX) (p : ℕ)
      [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap DX hij)]
      [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
      [∀ i : I, QuasiCompact (g i)] [∀ i : I, QuasiSeparated (g i)]
      [HasColimit (AlgebraicGeometry.Scheme.Etale.inverseImageDiagram DX cX F)]
      [HasColimit (AlgebraicGeometry.Scheme.Etale.HigherDirectImage.InverseSystem.diagram
        DX DS g hg cS F p)] (hcX : IsLimit cX) (hcS : IsLimit cS),
      IsIso (AlgebraicGeometry.Scheme.Etale.HigherDirectImage.InverseSystem.comparison
        DX DS g hg cX cS gX hgX F p))
