/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Hypercohomology.InverseSystem
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 59.52.1 -/
@[stacks 0EZM] #check
  (@AlgebraicGeometry.Scheme.Etale.etaleHypercohomology_colimit_affineTransition :
    ∀ [∀ {S T : Scheme.{u}} (f : T ⟶ S) (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
        (smallEtalePullback f).op.HasLeftKanExtension G]
      [∀ {S T : Scheme.{u}} (f : T ⟶ S),
        ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
      {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u})
      [∀ {i j : I} (hij : i ≤ j),
        IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
      [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
      [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
      [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology
        AddCommGrpCat.{u}]
      [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology
        AddCommGrpCat.{u}]
      (c : Cone D)
      [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
      [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
      (F : AlgebraicGeometry.Scheme.Etale.AbelianSheafComplexSystem D) (a p : ℤ)
      [HasColimit
        (AlgebraicGeometry.Scheme.Etale.hypercohomologyDiagram D F p)]
      [HasColimit
        (AlgebraicGeometry.Scheme.Etale.AbelianSheafComplexSystem.inverseImageComplexDiagram
          (D := D) c F)]
      (hc : IsLimit c) (hF : ∀ i, (F.obj i).IsStrictlyGE a),
      IsIso (AlgebraicGeometry.Scheme.Etale.complexComparison D F c p))

end

end
