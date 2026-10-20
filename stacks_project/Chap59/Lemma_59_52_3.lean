/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Hypercohomology.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}}
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
variable [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
variable [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasExt.{u} (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I, IsGrothendieckAbelian.{u}
    (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I,
    Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor (D.obj (OrderDual.toDual i)).smallEtaleTopology
          (globalEtale (D.obj (OrderDual.toDual i)))))
      (HomologicalComplex.quasiIso
        (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (Scheme.smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((Scheme.smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable (σ : D ⟶ (const (OrderDual I)).obj S)
variable (c : Cone D)
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u}
    (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [Functor.HasRightDerivedFunctor
    (Functor.RightDerived.Cochain.toDerived
      (siteAbelianSectionsFunctor c.pt.smallEtaleTopology (globalEtale c.pt)))
    (HomologicalComplex.quasiIso
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable [∀ i : I, IsGrothendieckAbelian.{u}
    (Sheaf (((const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)).smallEtaleTopology
      AddCommGrpCat.{u})]
variable [∀ i : I,
    Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor
          (((const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)).smallEtaleTopology
          (globalEtale (((const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)))))
      (HomologicalComplex.quasiIso
        (Sheaf (((const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)).smallEtaleTopology
          AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
variable (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (a p : ℤ)
variable [HasColimit (hypercohomologyDiagram D (pullbackComplexSystem D σ K) p)]
variable [HasColimit
    (AbelianSheafComplexSystem.inverseImageComplexDiagram (D := D) c
      (pullbackComplexSystem D σ K))]

/- Lemma 59.52.3: étale hypercohomology of pullbacks of a bounded-below complex `K` on `S`
commutes with a directed inverse limit of qcqs `S`-schemes with affine transitions. -/
@[stacks 0GIT] #check
  (AlgebraicGeometry.Scheme.Etale.etaleHypercohomology_colimit_baseChange D σ K c a p :
    IsLimit c → K.IsStrictlyGE a →
      IsIso (AlgebraicGeometry.Scheme.Etale.baseChangeComparison D σ K c p))

end AlgebraicGeometry.Scheme.Etale

end
