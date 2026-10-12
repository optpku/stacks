/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.«66_27_0_1_Comparison»
public import stacks_project.Chap66.«66_27_0_2_RingedSite»

/-!
# Étale localization of spaces-étale ringed sites

An étale morphism `f : X ⟶ Y` of algebraic spaces identifies the spaces-étale ringed site of
`X` with the localization of the spaces-étale ringed site of `Y` at the object
`spacesEtaleSite.mk f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The image of a structured arrow over `InverseObj W` under postcomposition along `f`. -/
def spacesEtaleLocalizationDiagramObj (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op (spacesEtaleLocalizationInverseObj f W))
      (smallEtaleInclusion X).op) :
    StructuredArrow (op W.left) (smallEtaleInclusion Y).op :=
  StructuredArrow.mk
    ((MorphismProperty.Over.homMk a.hom.unop.left sorry :
        (smallEtaleInclusion Y).obj
          ((Modules.restrictPostcompose f).obj a.right.unop) ⟶ W.left).op)

/-- Postcomposition of a small-étale arrow into `W.left` with the slice arrow `W.hom.left`
remains étale over `X`. -/
instance etale_comp_spacesEtaleSlice (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op W.left) (smallEtaleInclusion Y).op) :
    Etale (a.hom.unop.left ≫ W.hom.left) :=
  sorry

/-- Structured-arrow triangle in `Y_spaces,étale`: composing the chart morphism with the
structure morphism of `Z` recovers the structure morphism of the small étale chart. -/
theorem spacesEtaleLocalization_structuredArrow_w {Z : spacesEtaleSite Y}
    (a : StructuredArrow (op Z) (smallEtaleInclusion Y).op) :
    a.hom.unop.left ≫ Z.hom = a.right.unop.hom :=
  sorry

/-- Identity-on-scheme comparison from `restrictPostcompose` of
`smallEtaleSite.mk (a.hom.unop.left ≫ W.hom.left)` to the original Y-chart `a.right.unop`.
The witness is the structured-arrow triangle `a.hom.unop.left ≫ W.left.hom = a.right.unop.hom`. -/
def spacesEtaleLocalizationIsoHomSourceChartIso (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op W.left) (smallEtaleInclusion Y).op) :
    (Modules.restrictPostcompose f).obj
        (@smallEtaleSite.mk S X a.right.unop.left (a.hom.unop.left ≫ W.hom.left)
          (etale_comp_spacesEtaleSlice f W a)) ≅ a.right.unop :=
  { hom := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry
    inv := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The underlying scheme morphism of `spacesEtaleLocalizationIsoHomSourceChartIso` is the
identity. -/
@[simp]
theorem spacesEtaleLocalizationIsoHomSourceChartIso_hom_left (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op W.left) (smallEtaleInclusion Y).op) :
    (spacesEtaleLocalizationIsoHomSourceChartIso f W a).hom.left = 𝟙 _ :=
  rfl

/-- Transport of a structured arrow over `W.left` to one over `InverseObj W` by composing with
the slice arrow `W.hom.left : W.left.left ⟶ X`. This is `I_Y(W.left) → I_X(InverseObj W)`. -/
def spacesEtaleLocalizationDiagramObjInvAt (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op W.left) (smallEtaleInclusion Y).op) :
    StructuredArrow (op (spacesEtaleLocalizationInverseObj f W))
      (smallEtaleInclusion X).op :=
  StructuredArrow.mk
    ((MorphismProperty.Over.homMk a.hom.unop.left sorry :
        (smallEtaleInclusion X).obj
          (@smallEtaleSite.mk S X a.right.unop.left (a.hom.unop.left ≫ W.hom.left)
              (etale_comp_spacesEtaleSlice f W a)) ⟶
          spacesEtaleLocalizationInverseObj f W).op)

/-- Cone on the `𝒪_Y`-diagram at `W.left`, with point the `𝒪_X`-limit at `InverseObj W`.
Legs are `limit 𝒪_X ⟶ 𝒪_Y` via `spacesEtaleLocalizationDiagramObjInvAt`,
`Modules.restrictStructureMap`, and `spacesEtaleLocalizationIsoHomSourceChartIso` landing
on the original Y-chart `a.right`. Mathlib's `limit.lift F c : c.pt ⟶ limit F` therefore
yields `limit 𝒪_X ⟶ limit 𝒪_Y`, the reverse of the Hom sheaf arrow. -/
def spacesEtaleLocalizationIsoHomStructureSheaf_sourceCone (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    Cone
      (StructuredArrow.proj (op W.left) (smallEtaleInclusion Y).op ⋙
        (structureSheaf Y).obj) where
  pt :=
    limit
      (StructuredArrow.proj (op (spacesEtaleLocalizationInverseObj f W))
          (smallEtaleInclusion X).op ⋙
        (structureSheaf X).obj)
  π :=
    { app := fun a ↦
        limit.π
            (StructuredArrow.proj (op (spacesEtaleLocalizationInverseObj f W))
                (smallEtaleInclusion X).op ⋙
              (structureSheaf X).obj)
            (spacesEtaleLocalizationDiagramObjInvAt f W a) ≫
          (Modules.restrictStructureMap f).hom.app
            (op (@smallEtaleSite.mk S X a.right.unop.left
                (a.hom.unop.left ≫ W.hom.left)
                (etale_comp_spacesEtaleSlice f W a))) ≫
          (structureSheaf Y).obj.map
            (spacesEtaleLocalizationIsoHomSourceChartIso f W a).inv.op
      naturality := sorry }

/-- Cone on the `𝒪_X`-diagram at `InverseObj W`, with point the `𝒪_Y`-limit at `W.left`.
Legs are `limit 𝒪_Y ⟶ 𝒪_X` via `spacesEtaleLocalizationDiagramObj` and
`Modules.restrictStructureMapInv`. Because `limit.lift F c : c.pt ⟶ limit F`, this is the
cone whose lift is the Hom sheaf arrow `limit 𝒪_Y(W.left) ⟶ limit 𝒪_X(InverseObj W)`. -/
def spacesEtaleLocalizationIsoHomStructureSheaf_cone (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    Cone
      (StructuredArrow.proj (op (spacesEtaleLocalizationInverseObj f W))
          (smallEtaleInclusion X).op ⋙
        (structureSheaf X).obj) where
  pt :=
    limit
      (StructuredArrow.proj (op W.left) (smallEtaleInclusion Y).op ⋙
        (structureSheaf Y).obj)
  π :=
    { app := fun a ↦
        limit.π
            (StructuredArrow.proj (op W.left) (smallEtaleInclusion Y).op ⋙
              (structureSheaf Y).obj)
            (spacesEtaleLocalizationDiagramObj f W a) ≫
          (Modules.restrictStructureMapInv f).hom.app a.right
      naturality := sorry }

/-- Ran-coordinate Hom map `limit 𝒪_Y(W.left) ⟶ limit 𝒪_X(InverseObj W)`, as
`limit.lift` of `spacesEtaleLocalizationIsoHomStructureSheaf_cone`. -/
def spacesEtaleLocalizationIsoHomLimitMap (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    limit
        (StructuredArrow.proj (op W.left) (smallEtaleInclusion Y).op ⋙
          (structureSheaf Y).obj) ⟶
      limit
        (StructuredArrow.proj (op (spacesEtaleLocalizationInverseObj f W))
            (smallEtaleInclusion X).op ⋙
          (structureSheaf X).obj) :=
  limit.lift
    (StructuredArrow.proj (op (spacesEtaleLocalizationInverseObj f W))
        (smallEtaleInclusion X).op ⋙
      (structureSheaf X).obj)
    (spacesEtaleLocalizationIsoHomStructureSheaf_cone f W)

/-- Reverse Ran-coordinate map `limit 𝒪_X(InverseObj W) ⟶ limit 𝒪_Y(W.left)`, as
`limit.lift` of `spacesEtaleLocalizationIsoHomStructureSheaf_sourceCone`. -/
def spacesEtaleLocalizationIsoHomLimitMapInv (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    limit
        (StructuredArrow.proj (op (spacesEtaleLocalizationInverseObj f W))
            (smallEtaleInclusion X).op ⋙
          (structureSheaf X).obj) ⟶
      limit
        (StructuredArrow.proj (op W.left) (smallEtaleInclusion Y).op ⋙
          (structureSheaf Y).obj) :=
  limit.lift
    (StructuredArrow.proj (op W.left) (smallEtaleInclusion Y).op ⋙
      (structureSheaf Y).obj)
    (spacesEtaleLocalizationIsoHomStructureSheaf_sourceCone f W)

/-- Ran-coordinate identification of `𝒪_Y(W.left)` with `𝒪_X(InverseObj W)`. The forward
arrow is the Hom sheaf map; the reverse arrow is the lift of the `𝒪_Y`-diagram cone. -/
def spacesEtaleLocalizationIsoHomRanLimitIso (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f)) :
    limit
        (StructuredArrow.proj (op W.left) (smallEtaleInclusion Y).op ⋙
          (structureSheaf Y).obj) ≅
      limit
        (StructuredArrow.proj (op (spacesEtaleLocalizationInverseObj f W))
            (smallEtaleInclusion X).op ⋙
          (structureSheaf X).obj) where
  hom := spacesEtaleLocalizationIsoHomLimitMap f W
  inv := spacesEtaleLocalizationIsoHomLimitMapInv f W
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Forward component `𝒪_Y(W.left) ⟶ 𝒪_X(spacesEtaleLocalizationInverseObj f W.unop)`, obtained
from `ranObjObjIsoLimit` of `𝒪_Y` and `𝒪_X` and `spacesEtaleLocalizationIsoHomLimitMap`. -/
def spacesEtaleLocalizationIsoHomStructureSheaf_app (f : X ⟶ Y) [Etale f]
    (W : (Over (spacesEtaleSite.mk f))ᵒᵖ) :
    ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)).obj.obj W ⟶
      ((spacesEtaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
        (spacesEtaleTopology X)).obj (spacesStructureSheaf X) |>.obj.obj W :=
  EtaleRingedTopos.ringExtensionLift X (structureSheaf X)
    (spacesEtaleLocalizationInverseObj f W.unop)
    { pt := (spacesStructureSheaf Y).obj.obj (op W.unop.left)
      π :=
        { app := fun a ↦
            EtaleRingedTopos.ringExtensionEvaluation Y (structureSheaf Y)
              (spacesEtaleLocalizationDiagramObj f W.unop a).hom.unop ≫
            (Modules.restrictStructureMapInv f).hom.app a.right
          naturality := sorry } }

/-- Postcomposition of a slice arrow over `spacesEtaleRestriction f V` with `V.hom` remains
étale over `X`. -/
instance etale_comp_localization_slice (f : X ⟶ Y) [Etale f] (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleInclusion Y).op) :
    Etale (a.hom.unop.left ≫ V.hom) :=
  sorry

/-- Identity-on-scheme comparison from `restrictPostcompose` of
`smallEtaleSite.mk (a.hom.unop.left ≫ V.hom)` to the original Y-chart `a.right.unop`.
The witness is the structured-arrow triangle
`a.hom.unop.left ≫ ((spacesEtaleRestriction f).obj V).hom = a.right.unop.hom`. -/
def spacesEtaleLocalizationIsoInvChartIso (f : X ⟶ Y) [Etale f] (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleInclusion Y).op) :
    (Modules.restrictPostcompose f).obj
        (@smallEtaleSite.mk S X a.right.unop.left (a.hom.unop.left ≫ V.hom)
          (etale_comp_localization_slice f V a)) ≅ a.right.unop :=
  { hom := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry
    inv := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The underlying scheme morphism of `spacesEtaleLocalizationIsoInvChartIso` is the
identity. -/
@[simp]
theorem spacesEtaleLocalizationIsoInvChartIso_hom_left (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleInclusion Y).op) :
    (spacesEtaleLocalizationIsoInvChartIso f V a).hom.left = 𝟙 _ :=
  rfl

/-- The image of a structured arrow over `spacesEtaleRestriction f V` as a structured arrow
over `V`. -/
def spacesEtaleLocalizationDiagramObjInv (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleInclusion Y).op) :
    StructuredArrow (op V) (smallEtaleInclusion X).op :=
  StructuredArrow.mk
    ((MorphismProperty.Over.homMk a.hom.unop.left sorry :
        (smallEtaleInclusion X).obj
          (@smallEtaleSite.mk S X a.right.unop.left (a.hom.unop.left ≫ V.hom)
              (etale_comp_localization_slice f V a)) ⟶ V).op)

/-- Reindexing of `spacesEtaleLocalizationDiagramObj` along the unit iso
`V ≅ InverseObj (spacesEtaleLocalizationFunctor f |>.obj V)`, giving
`I_X(V) → I_Y(spacesEtaleRestriction f V)`. -/
def spacesEtaleLocalizationDiagramObjUnit (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X)
    (a : StructuredArrow (op V) (smallEtaleInclusion X).op) :
    StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleInclusion Y).op :=
  spacesEtaleLocalizationDiagramObj f ((spacesEtaleLocalizationFunctor f).obj V)
    ((StructuredArrow.map ((spacesEtaleLocalizationUnitIso f).hom.app V).op).obj a)

/-- Cone on the `𝒪_X`-diagram at `V`, with point the `𝒪_Y`-limit at
`spacesEtaleRestriction f V`. Legs are `limit 𝒪_Y ⟶ 𝒪_X` via
`spacesEtaleLocalizationDiagramObjUnit` and `Modules.restrictStructureMapInv`.
Mathlib's `limit.lift F c : c.pt ⟶ limit F` therefore yields
`limit 𝒪_Y ⟶ limit 𝒪_X`, the reverse of the Inv sheaf arrow. -/
def spacesEtaleLocalizationIsoInvStructureSheaf_sourceCone (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X) :
    Cone
      (StructuredArrow.proj (op V) (smallEtaleInclusion X).op ⋙
        (structureSheaf X).obj) where
  pt :=
    limit
      (StructuredArrow.proj (op ((spacesEtaleRestriction f).obj V))
          (smallEtaleInclusion Y).op ⋙
        (structureSheaf Y).obj)
  π :=
    { app := fun a ↦
        limit.π
            (StructuredArrow.proj (op ((spacesEtaleRestriction f).obj V))
                (smallEtaleInclusion Y).op ⋙
              (structureSheaf Y).obj)
            (spacesEtaleLocalizationDiagramObjUnit f V a) ≫
          (Modules.restrictStructureMapInv f).hom.app a.right
      naturality := sorry }

/-- Cone on the `𝒪_Y`-diagram at `spacesEtaleRestriction f V`, with point the corresponding
limit of `𝒪_X` at `V`. Legs land on the original Y-chart `a.right` after composing
`restrictStructureMap` with `spacesEtaleLocalizationIsoInvChartIso`. The induced
`limit.lift` is the Ran-coordinate Inv map `𝒪_X(V) ⟶ 𝒪_Y(spacesEtaleRestriction f V)`. -/
def spacesEtaleLocalizationIsoInvStructureSheaf_cone (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X) :
    Cone
      (StructuredArrow.proj (op ((spacesEtaleRestriction f).obj V))
          (smallEtaleInclusion Y).op ⋙
        (structureSheaf Y).obj) where
  pt :=
    limit
      (StructuredArrow.proj (op V) (smallEtaleInclusion X).op ⋙ (structureSheaf X).obj)
  π :=
    { app := fun a ↦
        limit.π
            (StructuredArrow.proj (op V) (smallEtaleInclusion X).op ⋙
              (structureSheaf X).obj)
            (spacesEtaleLocalizationDiagramObjInv f V a) ≫
          (Modules.restrictStructureMap f).hom.app
            (op (@smallEtaleSite.mk S X a.right.unop.left (a.hom.unop.left ≫ V.hom)
                (etale_comp_localization_slice f V a))) ≫
          (structureSheaf Y).obj.map
            (spacesEtaleLocalizationIsoInvChartIso f V a).inv.op
      naturality := sorry }

/-- Ran-coordinate Inv map `limit 𝒪_X(V) ⟶ limit 𝒪_Y(spacesEtaleRestriction f V)`, as
`limit.lift` of `spacesEtaleLocalizationIsoInvStructureSheaf_cone`. -/
def spacesEtaleLocalizationIsoInvLimitMap (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X) :
    limit
        (StructuredArrow.proj (op V) (smallEtaleInclusion X).op ⋙
          (structureSheaf X).obj) ⟶
      limit
        (StructuredArrow.proj (op ((spacesEtaleRestriction f).obj V))
            (smallEtaleInclusion Y).op ⋙
          (structureSheaf Y).obj) :=
  limit.lift
    (StructuredArrow.proj (op ((spacesEtaleRestriction f).obj V))
        (smallEtaleInclusion Y).op ⋙
      (structureSheaf Y).obj)
    (spacesEtaleLocalizationIsoInvStructureSheaf_cone f V)

/-- Reverse Ran-coordinate map `limit 𝒪_Y(spacesEtaleRestriction f V) ⟶ limit 𝒪_X(V)`, as
`limit.lift` of `spacesEtaleLocalizationIsoInvStructureSheaf_sourceCone`. -/
def spacesEtaleLocalizationIsoInvLimitMapInv (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X) :
    limit
        (StructuredArrow.proj (op ((spacesEtaleRestriction f).obj V))
            (smallEtaleInclusion Y).op ⋙
          (structureSheaf Y).obj) ⟶
      limit
        (StructuredArrow.proj (op V) (smallEtaleInclusion X).op ⋙
          (structureSheaf X).obj) :=
  limit.lift
    (StructuredArrow.proj (op V) (smallEtaleInclusion X).op ⋙ (structureSheaf X).obj)
    (spacesEtaleLocalizationIsoInvStructureSheaf_sourceCone f V)

/-- Ran-coordinate identification of `𝒪_X(V)` with `𝒪_Y(spacesEtaleRestriction f V)`. The
forward arrow is the Inv sheaf map. -/
def spacesEtaleLocalizationIsoInvRanLimitIso (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X) :
    limit
        (StructuredArrow.proj (op V) (smallEtaleInclusion X).op ⋙
          (structureSheaf X).obj) ≅
      limit
        (StructuredArrow.proj (op ((spacesEtaleRestriction f).obj V))
            (smallEtaleInclusion Y).op ⋙
          (structureSheaf Y).obj) where
  hom := spacesEtaleLocalizationIsoInvLimitMap f V
  inv := spacesEtaleLocalizationIsoInvLimitMapInv f V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse component `𝒪_X(V) ⟶ 𝒪_Y(spacesEtaleRestriction f V.unop)`, obtained from
`ranObjObjIsoLimit` of `𝒪_X` and `𝒪_Y` and `spacesEtaleLocalizationIsoInvLimitMap`. -/
def spacesEtaleLocalizationIsoInvStructureSheaf_app (f : X ⟶ Y) [Etale f]
    (V : (spacesEtaleSite X)ᵒᵖ) :
    (spacesStructureSheaf X).obj.obj V ⟶
      ((spacesEtaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X)
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))).obj
        ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) |>.obj.obj V :=
  EtaleRingedTopos.ringExtensionLift Y (structureSheaf Y)
    ((spacesEtaleRestriction f).obj V.unop)
    { pt := (spacesStructureSheaf X).obj.obj V
      π :=
        { app := fun a ↦
            EtaleRingedTopos.ringExtensionEvaluation X (structureSheaf X)
              (spacesEtaleLocalizationDiagramObjInv f V.unop a).hom.unop ≫
            (Modules.restrictStructureMap f).hom.app
              (op (@smallEtaleSite.mk S X a.right.unop.left (a.hom.unop.left ≫ V.unop.hom)
                (etale_comp_localization_slice f V.unop a))) ≫
            (structureSheaf Y).obj.map (spacesEtaleLocalizationIsoInvChartIso f V.unop a).inv.op
          naturality := sorry } }

/-- Forward structure-sheaf comparison from the restricted structure sheaf of `Y` to the
pushforward of `𝒪` along `spacesEtaleLocalizationInverse`. -/
def spacesEtaleLocalizationIsoHomStructureSheaf (f : X ⟶ Y) [Etale f] :
    (spacesStructureSheaf Y).over (spacesEtaleSite.mk f) ⟶
      ((spacesEtaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
        (spacesEtaleTopology X)).obj (spacesStructureSheaf X) :=
  ⟨{ app := fun W ↦ spacesEtaleLocalizationIsoHomStructureSheaf_app f W
     naturality := sorry }⟩

/-- Inverse structure-sheaf comparison from `𝒪` on `X_spaces,étale` to the pushforward of the
restricted structure sheaf of `Y` along `spacesEtaleLocalizationFunctor`. -/
def spacesEtaleLocalizationIsoInvStructureSheaf (f : X ⟶ Y) [Etale f] :
    spacesStructureSheaf X ⟶
      ((spacesEtaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X)
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))).obj
        ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) :=
  ⟨{ app := fun V ↦ spacesEtaleLocalizationIsoInvStructureSheaf_app f V
     naturality := sorry }⟩

/-- The morphism of ringed sites from `(X_spaces,étale, 𝒪_X)` to the localization of
`(Y_spaces,étale, 𝒪_Y)` at `X`. -/
def spacesEtaleLocalizationIsoHom (f : X ⟶ Y) [Etale f] :
    RingedSite.Hom (spacesRingedSite X)
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk f)) where
  base := spacesEtaleLocalizationInverse f
  structureSheafMap := spacesEtaleLocalizationIsoHomStructureSheaf f

/-- The morphism of ringed sites from the localization of `(Y_spaces,étale, 𝒪_Y)` at `X` to
`(X_spaces,étale, 𝒪_X)`. -/
def spacesEtaleLocalizationIsoInv (f : X ⟶ Y) [Etale f] :
    RingedSite.Hom ((spacesRingedSite Y).localization (spacesEtaleSite.mk f))
      (spacesRingedSite X) where
  base := spacesEtaleLocalizationFunctor f
  structureSheafMap := spacesEtaleLocalizationIsoInvStructureSheaf f

/-- Identification of spaces-étale ringed sites
`(X_spaces,étale, 𝒪_X) ≅ (Y_spaces,étale / X, 𝒪_Y restricted)` along an étale morphism of
algebraic spaces. -/
def spacesEtaleLocalizationIso (f : X ⟶ Y) [Etale f] :
    spacesRingedSite X ≅ (spacesRingedSite Y).localization (spacesEtaleSite.mk f) where
  hom := spacesEtaleLocalizationIsoHom f
  inv := spacesEtaleLocalizationIsoInv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The base functor of the forward ringed-site morphism is `spacesEtaleLocalizationInverse`. -/
@[simp]
theorem spacesEtaleLocalizationIso_hom_base (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationIso f).hom.base = spacesEtaleLocalizationInverse f :=
  rfl

/-- The base functor of the inverse ringed-site morphism is `spacesEtaleLocalizationFunctor`. -/
@[simp]
theorem spacesEtaleLocalizationIso_inv_base (f : X ⟶ Y) [Etale f] :
    (spacesEtaleLocalizationIso f).inv.base = spacesEtaleLocalizationFunctor f :=
  rfl

/-- The forward structure-sheaf comparison at `W` is
`spacesEtaleLocalizationIsoHomStructureSheaf_app`. -/
@[simp]
theorem spacesEtaleLocalizationIso_hom_structureSheaf_app (f : X ⟶ Y) [Etale f]
    (W : (Over (spacesEtaleSite.mk f))ᵒᵖ) :
    ((spacesEtaleLocalizationIso f).hom.structureSheafMap).hom.app W =
      spacesEtaleLocalizationIsoHomStructureSheaf_app f W :=
  rfl

/-- The inverse structure-sheaf comparison at `V` is
`spacesEtaleLocalizationIsoInvStructureSheaf_app`. -/
@[simp]
theorem spacesEtaleLocalizationIso_inv_structureSheaf_app (f : X ⟶ Y) [Etale f]
    (V : (spacesEtaleSite X)ᵒᵖ) :
    ((spacesEtaleLocalizationIso f).inv.structureSheafMap).hom.app V =
      spacesEtaleLocalizationIsoInvStructureSheaf_app f V :=
  rfl


end AlgebraicGeometry.AlgebraicSpace
