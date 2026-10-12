/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Hypercohomology.Pullback
public import ReasLib.CategoryTheory.Category.PreorderWithAdjoinedIdentities

/-! Colimits of étale hypercohomology for compatible inverse systems. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, IsGrothendieckAbelian.{u}
  (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S) (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [hAdj : ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable (F : AbelianSheafComplexSystem D)

/-- The directed diagram of stage hypercohomology, with identities adjoined. -/
def hypercohomologyDiagram (p : ℤ) : PreorderWithAdjoinedIdentities I ⥤ AddCommGrpCat.{u} :=
  PreorderWithAdjoinedIdentities.lift
    (fun i => etaleHypercohomology (D.obj (OrderDual.toDual i)) (F.obj i) p)
    (fun {i j} hij =>
      hypercohomologyPullback (OrderDualInverseSystem.transitionMap D hij) (F.obj i) p ≫
        etaleHypercohomology.map (F.transition hij) p) sorry

/-- Evaluating the stage diagram recovers the corresponding hypercohomology group. -/
theorem hypercohomologyDiagram_obj (p : ℤ) (i : I) :
    (hypercohomologyDiagram D F p).obj i =
      etaleHypercohomology (D.obj (OrderDual.toDual i)) (F.obj i) p := sorry

variable (c : Cone D)
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u}
  (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]

/-- The comparison from the colimit of stage hypercohomology to the limit complex. -/
def complexComparison (p : ℤ)
    [HasColimit (hypercohomologyDiagram D F p)]
    [HasColimit
      (AbelianSheafComplexSystem.inverseImageComplexDiagram (D := D) c F)] :
    colimit (hypercohomologyDiagram D F p) ⟶
      etaleHypercohomology c.pt
        (AbelianSheafComplexSystem.colimitInverseImageComplex (D := D) c F) p :=
  colimit.desc (hypercohomologyDiagram D F p)
    { pt := etaleHypercohomology c.pt
        (AbelianSheafComplexSystem.colimitInverseImageComplex (D := D) c F) p
      ι :=
        { app := fun i =>
            hypercohomologyPullback (c.π.app (OrderDual.toDual i)) (F.obj i) p ≫
              etaleHypercohomology.map
                (AbelianSheafComplexSystem.colimitInverseImageComplex_ι (D := D) c F i) p
          naturality := sorry } }

/-- Étale hypercohomology commutes with this affine-transition colimit. -/
theorem etaleHypercohomology_colimit_affineTransition
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
    [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
    (c : Cone D)
    [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
    (F : AbelianSheafComplexSystem D) (a p : ℤ)
    [HasColimit (hypercohomologyDiagram D F p)]
    [HasColimit
      (AbelianSheafComplexSystem.inverseImageComplexDiagram (D := D) c F)]
    (hc : IsLimit c) (hF : ∀ i, (F.obj i).IsStrictlyGE a) :
    IsIso (complexComparison D F c p) := sorry

end AlgebraicGeometry.Scheme.Etale

end
