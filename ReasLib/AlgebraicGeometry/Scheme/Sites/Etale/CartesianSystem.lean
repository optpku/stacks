/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafSystem
public import ReasLib.CategoryTheory.Category.PreorderWithAdjoinedIdentities

/-!
# Directed inverse systems of cartesian scheme squares

Directed inverse systems of cartesian squares of schemes, with chosen limit
cones forming a cartesian square and colimits of inverse images of set-valued
sheaves retaining the original composition-compatible transitions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Convert an `OrderDual`-indexed inverse system of schemes to the
`PreorderInverseSystem` presentation used by `SheafSystem`. -/
def orderDualToPreorderInverseSystem {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) :
    PreorderInverseSystem I Scheme.{u} where
  obj (iop : Iᵒᵖ) := D.obj (OrderDual.toDual iop.unop)
  map {i j : Iᵒᵖ} (f : i ⟶ j) :=
    D.map (homOfLE (OrderDual.toDual_le_toDual.mpr (leOfHom f.unop)))
  map_id := sorry
  map_comp := sorry

/-- The underlying scheme at `i` is unchanged by `orderDualToPreorderInverseSystem`. -/
theorem orderDualToPreorderInverseSystem_obj {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (i : I) :
    (orderDualToPreorderInverseSystem D).obj (Opposite.op i) =
      D.obj (OrderDual.toDual i) := sorry


section SetInverseImage

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [hAdjType : ∀ {S T : Scheme.{u}} (φ : T ⟶ S),
    ((smallEtalePullback φ).sheafPushforwardContinuous (Type (u + 1))
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

/-- Pullback of set-valued sheaves along an `OrderDual` inverse-system transition. -/
abbrev setTransitionPullback {i j : I} (hij : i ≤ j) :
    Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (D.obj (OrderDual.toDual j)).smallEtaleTopology (Type (u + 1)) :=
  (smallEtalePullback (OrderDualInverseSystem.transitionMap D hij)).sheafPullback
    (Type (u + 1)) (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology

variable [Nonempty I] [IsDirected I (· ≤ ·)]
variable (c : Cone D)

/-- Pullback of set-valued sheaves along a cone projection. -/
def setConePullback (i : I) :
    Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf c.pt.smallEtaleTopology (Type (u + 1)) :=
  @Functor.sheafPullback _ _ _ _
    (smallEtalePullback (c.π.app (OrderDual.toDual i))) (Type (u + 1)) _
    (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology
    (smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual i)))
    (hAdjType (c.π.app (OrderDual.toDual i)))

/-- Continuity of small étale pullback along a cone projection. -/
instance setConeLeg_isContinuous (i : I) :
    (smallEtalePullback (c.π.app (OrderDual.toDual i))).IsContinuous
      (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology :=
  smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual i))

/-- The small étale pushforward along a cone projection is a right adjoint. -/
instance setConeLeg_sheafPushforward_isRightAdjoint (i : I) :
    ((smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
        (Type (u + 1)) (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology).IsRightAdjoint :=
  hAdjType (c.π.app (OrderDual.toDual i))

/-- Sheaf adjunction along a cone projection, with continuity supplied explicitly. -/
def setConeLegSheafAdjunction (i : I) :
    (smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPullback (Type (u + 1))
        (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology ⊣
      (smallEtalePullback (c.π.app (OrderDual.toDual i))).sheafPushforwardContinuous
        (Type (u + 1)) (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology :=
  @Functor.sheafAdjunctionContinuous
    (D.obj (OrderDual.toDual i)).Etale inferInstance
    c.pt.Etale inferInstance
    (smallEtalePullback (c.π.app (OrderDual.toDual i))) (Type (u + 1)) inferInstance
    (D.obj (OrderDual.toDual i)).smallEtaleTopology c.pt.smallEtaleTopology
    (smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual i)))
    (hAdjType (c.π.app (OrderDual.toDual i)))

/-- Composite cone pullbacks identify with pullback along the composite projection. -/
def setConePullbackCompIso {i j : I} (hij : i ≤ j) :
    SheafSystem.pullback (orderDualToPreorderInverseSystem D) hij ⋙
        setConePullback D c j ≅
      setConePullback D c i :=
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
      (Type (u + 1)) (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology)
    (setConeLegSheafAdjunction D c j) (setConeLegSheafAdjunction D c i)
    (@Functor.sheafPushforwardContinuousComp'
      (D.obj (OrderDual.toDual i)).Etale inferInstance
      (D.obj (OrderDual.toDual j)).Etale inferInstance
      c.pt.Etale inferInstance
      (smallEtalePullback (OrderDualInverseSystem.transitionMap D hij))
      (smallEtalePullback (c.π.app (OrderDual.toDual j)))
      (smallEtalePullback (c.π.app (OrderDual.toDual i))) siteIso
      (Type (u + 1)) inferInstance
      (D.obj (OrderDual.toDual i)).smallEtaleTopology (D.obj (OrderDual.toDual j)).smallEtaleTopology
      c.pt.smallEtaleTopology
      inferInstance
      (smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual j)))
      (smallEtalePullback_isContinuous (c.π.app (OrderDual.toDual i))))

variable (Fsys : SheafSystem (orderDualToPreorderInverseSystem D))

/-- The diagram of inverse images `p_i⁻¹ F_i`, retaining every original transition
and adjoining genuine categorical identities. -/
def setInverseImageDiagram :
    PreorderWithAdjoinedIdentities I ⥤ Sheaf c.pt.smallEtaleTopology (Type (u + 1)) :=
  PreorderWithAdjoinedIdentities.lift
    (fun i => (setConePullback D c i).obj (Fsys.obj i))
    (fun {i j} hij => (setConePullbackCompIso D c hij).inv.app (Fsys.obj i) ≫
      (setConePullback D c j).map (Fsys.transition hij)) sorry

/-- The colimit sheaf `F = colim p_i⁻¹ F_i` on the small étale site of the limit. -/
def setColimitInverseImage
    [HasColimit (setInverseImageDiagram D c Fsys)] :
    Sheaf c.pt.smallEtaleTopology (Type (u + 1)) :=
  colimit (setInverseImageDiagram D c Fsys)

/-- `setColimitInverseImage` is the colimit of `setInverseImageDiagram`. -/
theorem setColimitInverseImage_eq
    [HasColimit (setInverseImageDiagram D c Fsys)] :
    setColimitInverseImage D c Fsys = colimit (setInverseImageDiagram D c Fsys) := sorry

/-- The object of `setInverseImageDiagram` at `i` is the inverse image of the
stage sheaf along the cone projection. -/
theorem setInverseImageDiagram_obj (i : I) :
    (setInverseImageDiagram D c Fsys).obj i =
      (setConePullback D c i).obj (Fsys.obj i) := sorry

end SetInverseImage

/-- A directed inverse system of cartesian squares of schemes
`X_i ← Y_i → T_i → S_i ← X_i`, together with chosen limit cones and a
cartesian limit square. -/
structure InverseSystemCartesianSquare (I : Type u)
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] where
  /-- Inverse system of the schemes `X_i`. -/
  DX : OrderDual I ⥤ Scheme.{u}
  /-- Inverse system of the schemes `Y_i`. -/
  DY : OrderDual I ⥤ Scheme.{u}
  /-- Inverse system of the schemes `S_i`. -/
  DS : OrderDual I ⥤ Scheme.{u}
  /-- Inverse system of the schemes `T_i`. -/
  DT : OrderDual I ⥤ Scheme.{u}
  /-- Stage morphisms `f_i : X_i ⟶ S_i`. -/
  f : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i)
  /-- Stage morphisms `h_i : Y_i ⟶ X_i`. -/
  h : ∀ i : I, DY.obj (OrderDual.toDual i) ⟶ DX.obj (OrderDual.toDual i)
  /-- Stage morphisms `e_i : Y_i ⟶ T_i`. -/
  e : ∀ i : I, DY.obj (OrderDual.toDual i) ⟶ DT.obj (OrderDual.toDual i)
  /-- Stage morphisms `g_i : T_i ⟶ S_i`. -/
  g : ∀ i : I, DT.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i)
  /-- Each stage square commutes. -/
  stage_comm : ∀ i : I, h i ≫ f i = e i ≫ g i
  /-- Each stage square is cartesian. -/
  stage_isPullback : ∀ i : I, IsPullback (h i) (e i) (f i) (g i)
  /-- The morphisms `f_i` commute with inverse-system transitions. -/
  f_natural : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DX hij ≫ f i =
      f j ≫ OrderDualInverseSystem.transitionMap DS hij
  /-- The morphisms `h_i` commute with inverse-system transitions. -/
  h_natural : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DY hij ≫ h i =
      h j ≫ OrderDualInverseSystem.transitionMap DX hij
  /-- The morphisms `e_i` commute with inverse-system transitions. -/
  e_natural : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DY hij ≫ e i =
      e j ≫ OrderDualInverseSystem.transitionMap DT hij
  /-- The morphisms `g_i` commute with inverse-system transitions. -/
  g_natural : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DT hij ≫ g i =
      g j ≫ OrderDualInverseSystem.transitionMap DS hij
  /-- Chosen limit cone of the `X_i`. -/
  cX : Cone DX
  /-- Chosen limit cone of the `Y_i`. -/
  cY : Cone DY
  /-- Chosen limit cone of the `S_i`. -/
  cS : Cone DS
  /-- Chosen limit cone of the `T_i`. -/
  cT : Cone DT
  /-- The cone `cX` is a limit cone. -/
  hcX : IsLimit cX
  /-- The cone `cY` is a limit cone. -/
  hcY : IsLimit cY
  /-- The cone `cS` is a limit cone. -/
  hcS : IsLimit cS
  /-- The cone `cT` is a limit cone. -/
  hcT : IsLimit cT
  /-- Limit morphism `f : X ⟶ S`. -/
  fLim : cX.pt ⟶ cS.pt
  /-- Limit morphism `h : Y ⟶ X`. -/
  hLim : cY.pt ⟶ cX.pt
  /-- Limit morphism `e : Y ⟶ T`. -/
  eLim : cY.pt ⟶ cT.pt
  /-- Limit morphism `g : T ⟶ S`. -/
  gLim : cT.pt ⟶ cS.pt
  /-- The limit square commutes. -/
  limit_comm : hLim ≫ fLim = eLim ≫ gLim
  /-- Projections of `cX` and `cS` intertwine `fLim` and the stage maps `f_i`. -/
  fLim_comm : ∀ i : I,
    cX.π.app (OrderDual.toDual i) ≫ f i = fLim ≫ cS.π.app (OrderDual.toDual i)
  /-- Projections of `cY` and `cX` intertwine `hLim` and the stage maps `h_i`. -/
  hLim_comm : ∀ i : I,
    cY.π.app (OrderDual.toDual i) ≫ h i = hLim ≫ cX.π.app (OrderDual.toDual i)
  /-- Projections of `cY` and `cT` intertwine `eLim` and the stage maps `e_i`. -/
  eLim_comm : ∀ i : I,
    cY.π.app (OrderDual.toDual i) ≫ e i = eLim ≫ cT.π.app (OrderDual.toDual i)
  /-- Projections of `cT` and `cS` intertwine `gLim` and the stage maps `g_i`. -/
  gLim_comm : ∀ i : I,
    cT.π.app (OrderDual.toDual i) ≫ g i = gLim ≫ cS.π.app (OrderDual.toDual i)
  /-- The limit square is cartesian. -/
  limit_isPullback : IsPullback hLim eLim fLim gLim

namespace InverseSystemCartesianSquare

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- Assemble an inverse system of cartesian squares from its functors, stage
morphisms, limit cones, and cartesian data. -/
def ofStage
    (DX DY DS DT : OrderDual I ⥤ Scheme.{u})
    (f : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
    (h : ∀ i : I, DY.obj (OrderDual.toDual i) ⟶ DX.obj (OrderDual.toDual i))
    (e : ∀ i : I, DY.obj (OrderDual.toDual i) ⟶ DT.obj (OrderDual.toDual i))
    (g : ∀ i : I, DT.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
    (stage_comm : ∀ i : I, h i ≫ f i = e i ≫ g i)
    (stage_isPullback : ∀ i : I, IsPullback (h i) (e i) (f i) (g i))
    (f_natural : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DX hij ≫ f i =
        f j ≫ OrderDualInverseSystem.transitionMap DS hij)
    (h_natural : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DY hij ≫ h i =
        h j ≫ OrderDualInverseSystem.transitionMap DX hij)
    (e_natural : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DY hij ≫ e i =
        e j ≫ OrderDualInverseSystem.transitionMap DT hij)
    (g_natural : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DT hij ≫ g i =
        g j ≫ OrderDualInverseSystem.transitionMap DS hij)
    (cX : Cone DX) (cY : Cone DY) (cS : Cone DS) (cT : Cone DT)
    (hcX : IsLimit cX) (hcY : IsLimit cY) (hcS : IsLimit cS) (hcT : IsLimit cT)
    (fLim : cX.pt ⟶ cS.pt) (hLim : cY.pt ⟶ cX.pt)
    (eLim : cY.pt ⟶ cT.pt) (gLim : cT.pt ⟶ cS.pt)
    (limit_comm : hLim ≫ fLim = eLim ≫ gLim)
    (fLim_comm : ∀ i : I,
      cX.π.app (OrderDual.toDual i) ≫ f i = fLim ≫ cS.π.app (OrderDual.toDual i))
    (hLim_comm : ∀ i : I,
      cY.π.app (OrderDual.toDual i) ≫ h i = hLim ≫ cX.π.app (OrderDual.toDual i))
    (eLim_comm : ∀ i : I,
      cY.π.app (OrderDual.toDual i) ≫ e i = eLim ≫ cT.π.app (OrderDual.toDual i))
    (gLim_comm : ∀ i : I,
      cT.π.app (OrderDual.toDual i) ≫ g i = gLim ≫ cS.π.app (OrderDual.toDual i))
    (limit_isPullback : IsPullback hLim eLim fLim gLim) :
    InverseSystemCartesianSquare I where
  DX := DX
  DY := DY
  DS := DS
  DT := DT
  f := f
  h := h
  e := e
  g := g
  stage_comm := stage_comm
  stage_isPullback := stage_isPullback
  f_natural := f_natural
  h_natural := h_natural
  e_natural := e_natural
  g_natural := g_natural
  cX := cX
  cY := cY
  cS := cS
  cT := cT
  hcX := hcX
  hcY := hcY
  hcS := hcS
  hcT := hcT
  fLim := fLim
  hLim := hLim
  eLim := eLim
  gLim := gLim
  limit_comm := limit_comm
  fLim_comm := fLim_comm
  hLim_comm := hLim_comm
  eLim_comm := eLim_comm
  gLim_comm := gLim_comm
  limit_isPullback := limit_isPullback

variable (C : InverseSystemCartesianSquare I)

/-- Stage squares of `C` commute and are cartesian. -/
theorem spec_stage (i : I) :
    C.h i ≫ C.f i = C.e i ≫ C.g i ∧ IsPullback (C.h i) (C.e i) (C.f i) (C.g i) :=
  ⟨C.stage_comm i, C.stage_isPullback i⟩

/-- The limit square of `C` commutes and is cartesian. -/
theorem spec_limit :
    C.hLim ≫ C.fLim = C.eLim ≫ C.gLim ∧ IsPullback C.hLim C.eLim C.fLim C.gLim :=
  ⟨C.limit_comm, C.limit_isPullback⟩

end InverseSystemCartesianSquare

end AlgebraicGeometry.Scheme.Etale

end
