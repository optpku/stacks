/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import ReasLib.CategoryTheory.Category.PreorderWithAdjoinedIdentities

/-!
# Inverse images of abelian étale sheaves along affine-transition limits

This module owns the compatible abelian sheaf system on a directed inverse
system of schemes, together with the inverse-image diagram and colimit sheaf
`F = colim f_i⁻¹ F_i` on the small étale site of the limit.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v}]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{v}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [hAdj : ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{v}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

/-- Pullback of abelian sheaves along a transition of an `OrderDual`-indexed inverse system. -/
abbrev transitionPullback {i j : I} (hij : i ≤ j) :
    Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v} ⥤
      Sheaf (D.obj (OrderDual.toDual j)).smallEtaleTopology AddCommGrpCat.{v} :=
  (smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafPullback
    AddCommGrpCat.{v} (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology

/-- Successive transition pullbacks are canonically isomorphic to pullback along the
composite transition. -/
def transitionPullbackCompIso {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transitionPullback D hij ⋙ transitionPullback D hjk ≅
      transitionPullback D (le_trans hij hjk) :=
  let mapEq :
      OrderDualInverseSystem.transitionMap D (le_trans hij hjk) =
        OrderDualInverseSystem.transitionMap D hjk ≫
          OrderDualInverseSystem.transitionMap D hij :=
    OrderDualInverseSystem.transitionMap_comp D hij hjk
  let siteIso :
      smallEtalePullback (OrderDualInverseSystem.transitionMap D hij) ⋙
          smallEtalePullback (OrderDualInverseSystem.transitionMap D hjk) ≅
        smallEtalePullback (OrderDualInverseSystem.transitionMap D (le_trans hij hjk)) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (OrderDualInverseSystem.transitionMap D hjk)
        (OrderDualInverseSystem.transitionMap D hij)).symm ≪≫
      eqToIso (congrArg smallEtalePullback mapEq.symm)
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafAdjunctionContinuous
      AddCommGrpCat.{v} (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology)
    ((smallEtalePullback (OrderDualInverseSystem.transitionMap D hjk)).sheafAdjunctionContinuous
      AddCommGrpCat.{v} (D.obj (OrderDual.toDual j)).smallEtaleTopology (D.obj (OrderDual.toDual k)).smallEtaleTopology)
    ((smallEtalePullback
        (OrderDualInverseSystem.transitionMap D (le_trans hij hjk))).sheafAdjunctionContinuous
      AddCommGrpCat.{v} (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual k)).smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso AddCommGrpCat.{v}
      (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology
      (D.obj (OrderDual.toDual k)).smallEtaleTopology)

/-- A compatible system of abelian sheaves on the small étale sites of a directed inverse
system of schemes. -/
structure AbelianSheafSystem where
  /-- The abelian sheaf on the small étale site of the scheme at `i`. -/
  obj (i : I) :
    Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v}
  /-- The transition from the pullback of the sheaf at `i` to the sheaf at `j`. -/
  transition {i j : I} (hij : i ≤ j) :
    (transitionPullback D hij).obj (obj i) ⟶ obj j
  /-- Transition morphisms satisfy the three-index pullback cocycle law. -/
  transition_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (transitionPullbackCompIso D hij hjk).hom.app (obj i) ≫
        transition (le_trans hij hjk) =
      (transitionPullback D hjk).map (transition hij) ≫ transition hjk

namespace AbelianSheafSystem

variable {D : OrderDual I ⥤ Scheme.{u}}
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v}]

/-- Construct an abelian sheaf system from stage sheaves, transitions, and the cocycle law. -/
def of
    (obj : (i : I) →
      Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v})
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (transitionPullback D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (transitionPullbackCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (transitionPullback D hjk).map (transition hij) ≫ transition hjk) :
    AbelianSheafSystem D where
  obj := obj
  transition := transition
  transition_comp := transition_comp

/-- The stage sheaf of `AbelianSheafSystem.of` is the supplied stage sheaf. -/
theorem of_obj
    (obj : (i : I) →
      Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v})
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (transitionPullback D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (transitionPullbackCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (transitionPullback D hjk).map (transition hij) ≫ transition hjk)
    (i : I) :
    (of obj transition transition_comp).obj i = obj i := sorry

/-- The transition of `AbelianSheafSystem.of` is the supplied transition morphism. -/
theorem of_transition
    (obj : (i : I) →
      Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v})
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (transitionPullback D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (transitionPullbackCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (transitionPullback D hjk).map (transition hij) ≫ transition hjk)
    {i j : I} (hij : i ≤ j) :
    (of obj transition transition_comp).transition hij = transition hij := sorry

end AbelianSheafSystem


variable [Nonempty I] [IsDirected I (· ≤ ·)]
variable (c : Cone D)
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{v}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{v}]
variable (F : AbelianSheafSystem D)

/-- Pullback of abelian sheaves along a cone projection `f_i : X ⟶ X_i`. -/
def conePullback (i : I) :
    Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{v} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{v} :=
  @Functor.sheafPullback _ _ _ _
    (smallEtalePullback (c.π.app (OrderDual.toDual i))) AddCommGrpCat.{v} _
    (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology
    (smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual i)))
    (hAdj (c.π.app (OrderDual.toDual i)))

/-- Continuity of small étale pullback along a cone projection. -/
instance coneLeg_isContinuous (i : I) :
    (smallEtalePullback (c.π.app (OrderDual.toDual i))).IsContinuous
      (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology :=
  smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual i))

/-- The small étale pushforward along a cone projection is a right adjoint. -/
instance coneLeg_sheafPushforward_isRightAdjoint (i : I) :
    ((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
        AddCommGrpCat.{v} (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology).IsRightAdjoint :=
  hAdj (c.π.app (OrderDual.toDual i))

/-- Sheaf adjunction along a cone projection, with continuity supplied explicitly. -/
def coneLegSheafAdjunction (i : I) :
    (smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPullback AddCommGrpCat.{v}
        (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology ⊣
      (smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
        AddCommGrpCat.{v} (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology :=
  @Functor.sheafAdjunctionContinuous
    (D.obj (OrderDual.toDual i)).Etale inferInstance
    c.pt.Etale inferInstance
    (smallEtalePullback (c.π.app (OrderDual.toDual i))) AddCommGrpCat.{v} inferInstance
    (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology
    (smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual i)))
    (hAdj (c.π.app (OrderDual.toDual i)))

/-- Composite cone pullbacks identify with pullback along the composite projection. -/
def conePullbackCompIso {i j : I} (hij : i ≤ j) :
    transitionPullback D hij ⋙ conePullback D c j ≅ conePullback D c i :=
  let mapEq :
      c.π.app (OrderDual.toDual j) ≫
          OrderDualInverseSystem.transitionMap D hij =
        c.π.app (OrderDual.toDual i) :=
    c.w (homOfLE (OrderDual.toDual_le_toDual.mpr hij))
  let siteIso :
      smallEtalePullback (OrderDualInverseSystem.transitionMap D hij) ⋙
          smallEtalePullback (c.π.app (OrderDual.toDual j)) ≅
        smallEtalePullback (c.π.app (OrderDual.toDual i)) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app (OrderDual.toDual j)) (OrderDualInverseSystem.transitionMap D hij)).symm ≪≫
      eqToIso (congrArg smallEtalePullback mapEq)
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafAdjunctionContinuous
      AddCommGrpCat.{v} (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology)
    (coneLegSheafAdjunction D c j) (coneLegSheafAdjunction D c i)
    (@Functor.sheafPushforwardContinuousComp'
      (D.obj (OrderDual.toDual i)).Etale inferInstance
      (D.obj (OrderDual.toDual j)).Etale inferInstance
      c.pt.Etale inferInstance
      (smallEtalePullback (OrderDualInverseSystem.transitionMap D hij))
      (smallEtalePullback (c.π.app (OrderDual.toDual j)))
      (smallEtalePullback (c.π.app (OrderDual.toDual i))) siteIso
      AddCommGrpCat.{v} inferInstance
      (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology
      c.pt.smallEtaleTopology
      inferInstance
      (smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual j)))
      (smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual i))))

/-- The diagram of inverse images `f_i⁻¹ F_i`, retaining the original transitions and
adjoining genuine categorical identities. -/
def inverseImageDiagram :
    PreorderWithAdjoinedIdentities I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{v} :=
  PreorderWithAdjoinedIdentities.lift
    (fun i => (conePullback D c i).obj (F.obj i))
    (fun {i j} hij => (conePullbackCompIso D c hij).inv.app (F.obj i) ≫
      (conePullback D c j).map (F.transition hij)) sorry

/-- The colimit sheaf `F = colim_i f_i⁻¹ F_i` on the small étale site of the limit. -/
def colimitInverseImage
    [HasColimit (inverseImageDiagram D c F)] :
    Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{v} :=
  colimit (inverseImageDiagram D c F)

/-- The canonical map `f_i⁻¹ F_i ⟶ colim_j f_j⁻¹ F_j`. -/
def colimitInverseImage_ι (i : I)
    [HasColimit (inverseImageDiagram D c F)] :
    (inverseImageDiagram D c F).obj i ⟶ colimitInverseImage D c F :=
  colimit.ι (inverseImageDiagram D c F) i

/-- The component of `colimitInverseImage_ι` is the colimit inclusion of the inverse-image
diagram. -/
theorem colimitInverseImage_ι_eq (i : I)
    [HasColimit (inverseImageDiagram D c F)] :
    colimitInverseImage_ι D c F i = colimit.ι (inverseImageDiagram D c F) i := sorry

end AlgebraicGeometry.Scheme.Etale

end
