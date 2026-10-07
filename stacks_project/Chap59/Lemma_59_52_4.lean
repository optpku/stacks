module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.ComplexInverseSystem
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
universe u

/- Lemma 59.52.4: for the directed affine-transition system of qcqs morphisms with
both limiting cones, the canonical upper-tail colimit comparison for the pullbacks
of a cohomologically bounded-below complex is an isomorphism in every integer degree. -/
@[stacks 0GIU] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImageComplex_colimit_pullback :
    ∀ {I : Type u} [Preorder I],
    ∀ (DX DS : OrderDual I ⥤ Scheme.{u}),
    ∀ [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}],
    ∀ [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}],
    ∀ [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}],
    ∀ [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}],
    ∀ [∀ i : I, IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})],
    ∀ [∀ i : I, IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})],
    ∀ [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G],
    ∀ [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint],
    ∀ (g : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i)),
    ∀ (hg : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DX hij ≫ g i =
      g j ≫ OrderDualInverseSystem.transitionMap DS hij),
    ∀ [∀ i : I,
    ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
      (DS.obj (OrderDual.toDual i)).smallEtaleTopology
      (DX.obj (OrderDual.toDual i)).smallEtaleTopology).Additive],
    ∀ [∀ i : I,
    Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived
        ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
          (DS.obj (OrderDual.toDual i)).smallEtaleTopology
          (DX.obj (OrderDual.toDual i)).smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ))],
    ∀ (cX : Cone DX) (cS : Cone DS),
    ∀ (gX : cX.pt ⟶ cS.pt),
    ∀ (hgX : ∀ i : I,
    cX.π.app (OrderDual.toDual i) ≫ g i = gX ≫ cS.π.app (OrderDual.toDual i)),
    ∀ [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}],
    ∀ [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}],
    ∀ [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}],
    ∀ [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}],
    ∀ [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})],
    ∀ [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u})],
    ∀ [((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
      cS.pt.smallEtaleTopology cX.pt.smallEtaleTopology).Additive],
    ∀ [Functor.HasRightDerivedFunctor
    (Functor.RightDerived.Cochain.toDerived
      ((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
        cS.pt.smallEtaleTopology cX.pt.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))],
    ∀ (i0 : I),
    ∀ (K0 : CochainComplex
    (Sheaf (DX.obj (OrderDual.toDual i0)).smallEtaleTopology AddCommGrpCat.{u}) ℤ),
    ∀ (p : ℤ),
    ∀ [HasColimit (higherDirectImageComplex_pullbackDiagram DX DS g hg cS i0 K0 p)]
      [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap DX hij)]
      [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
      [∀ i : I, QuasiCompact (g i)] [∀ i : I, QuasiSeparated (g i)]
      [QuasiCompact gX] [QuasiSeparated gX] [Nonempty I] [IsDirected I (· ≤ ·)]
      (hcX : IsLimit cX) (hcS : IsLimit cS) (a : ℤ),
      K0.IsGE a →
        IsIso (higherDirectImageComplex_pullbackComparison DX DS g hg cX cS gX hgX i0 K0 p))
