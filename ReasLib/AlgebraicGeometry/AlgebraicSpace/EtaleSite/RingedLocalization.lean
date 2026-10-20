module

public import ReasLib.CategoryTheory.Sites.Ringed.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Localization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction

/-!
# Étale localization of spaces-étale ringed sites

An étale morphism of algebraic spaces identifies the spaces-étale ringed site of its domain
with the slice ringed site of its codomain, including the restricted structure sheaf.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Structured-arrow triangle in `Y_spaces,étale`: composing the chart morphism with the
structure morphism of `Z` recovers the structure morphism of the small étale chart. -/
private theorem spacesEtaleLocalization_structuredArrow_w {Z : spacesEtaleSite Y}
    (a : StructuredArrow (op Z) (smallEtaleToSpaces Y).op) :
    a.hom.unop.left ≫ Z.hom = a.right.unop.hom :=
  sorry

/-- Postcomposition of a chart over a slice object commutes with its map to the base. -/
private theorem spacesEtaleLocalizationDiagramObj_w (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op (spacesEtaleLocalizationInverseObj f W))
      (smallEtaleToSpaces X).op) :
    a.hom.unop.left ≫ W.left.hom = a.right.unop.hom ≫ f :=
  sorry

/-- The image of a structured arrow over `InverseObj W` under postcomposition along `f`. -/
private def spacesEtaleLocalizationDiagramObj (f : X ⟶ Y) [Etale f]
    (W : Over (spacesEtaleSite.mk f))
    (a : StructuredArrow (op (spacesEtaleLocalizationInverseObj f W))
      (smallEtaleToSpaces X).op) :
    StructuredArrow (op W.left) (smallEtaleToSpaces Y).op :=
  StructuredArrow.mk
    ((MorphismProperty.Over.homMk a.hom.unop.left (spacesEtaleLocalizationDiagramObj_w f W a) :
        (smallEtaleToSpaces Y).obj
          ((Modules.restrictPostcompose f).obj a.right.unop) ⟶ W.left).op)

/-- The forward structure-sheaf component is the lift of the chart evaluations followed by
identity-on-sections étale restriction. -/
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
      (smallEtaleToSpaces Y).op) :
    Etale (a.hom.unop.left ≫ V.hom) :=
  sorry

/-- Identity-on-scheme comparison from `restrictPostcompose` of
`smallEtaleSite.mk (a.hom.unop.left ≫ V.hom)` to the original Y-chart `a.right.unop`.
The witness is the structured-arrow triangle
`a.hom.unop.left ≫ ((spacesEtaleRestriction f).obj V).hom = a.right.unop.hom`. -/
private def spacesEtaleLocalizationIsoInvChartIso (f : X ⟶ Y) [Etale f] (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleToSpaces Y).op) :
    (Modules.restrictPostcompose f).obj
        (smallEtaleSite.mk (U := a.right.unop.left) (a.hom.unop.left ≫ V.hom)
          (etale_comp_localization_slice f V a)) ≅ a.right.unop :=
  MorphismProperty.CostructuredArrow.isoMk (Iso.refl _) trivial trivial (by
    exact (congrArg (fun k ↦ k ≫ a.right.unop.hom)
      ((ofOverFunctor S).map_id a.right.unop.left)).trans
        ((Category.id_comp _).trans
          ((spacesEtaleLocalization_structuredArrow_w a).symm.trans
            (Category.assoc _ _ _).symm)))

/-- The image of a structured arrow over `spacesEtaleRestriction f V` as a structured arrow
over `V`. -/
private def spacesEtaleLocalizationDiagramObjInv (f : X ⟶ Y) [Etale f]
    (V : spacesEtaleSite X)
    (a : StructuredArrow (op ((spacesEtaleRestriction f).obj V))
      (smallEtaleToSpaces Y).op) :
    StructuredArrow (op V) (smallEtaleToSpaces X).op :=
  StructuredArrow.mk
    ((MorphismProperty.Over.homMk a.hom.unop.left rfl :
        (smallEtaleToSpaces X).obj
          (smallEtaleSite.mk (U := a.right.unop.left) (a.hom.unop.left ≫ V.hom)
              (etale_comp_localization_slice f V a)) ⟶ V).op)

/-- The inverse structure-sheaf component is the lift of chart evaluations and
identity-on-sections restriction, transported along the identity chart comparison. -/
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
              (op (smallEtaleSite.mk (U := a.right.unop.left) (a.hom.unop.left ≫ V.unop.hom)
                (etale_comp_localization_slice f V.unop a))) ≫
            (structureSheaf Y).obj.map (spacesEtaleLocalizationIsoInvChartIso f V.unop a).inv.op
          naturality := sorry } }

/-- Forward structure-sheaf comparison from the restricted structure sheaf of `Y` to the
pushforward of `𝒪` along `spacesEtaleLocalizationInverse`. -/
@[expose]
def spacesEtaleLocalizationIsoHomStructureSheaf (f : X ⟶ Y) [Etale f] :
    (spacesStructureSheaf Y).over (spacesEtaleSite.mk f) ⟶
      ((spacesEtaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
        (spacesEtaleTopology X)).obj (spacesStructureSheaf X) :=
  ⟨{ app := fun W ↦ spacesEtaleLocalizationIsoHomStructureSheaf_app f W
     naturality := sorry }⟩

/-- Inverse structure-sheaf comparison from `𝒪` on `X_spaces,étale` to the pushforward of the
restricted structure sheaf of `Y` along `spacesEtaleLocalizationFunctor`. -/
@[expose]
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
@[expose]
def spacesEtaleLocalizationIsoHom (f : X ⟶ Y) [Etale f] :
    RingedSiteMap (spacesEtaleTopology X) (spacesStructureSheaf X)
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
      ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) where
  base := spacesEtaleLocalizationInverse f
  isMorphismOfSites := spacesEtaleLocalizationInverse.instIsMorphismOfSites f
  structureSheafMap := spacesEtaleLocalizationIsoHomStructureSheaf f

/-- The morphism of ringed sites from the localization of `(Y_spaces,étale, 𝒪_Y)` at `X` to
`(X_spaces,étale, 𝒪_X)`. -/
@[expose]
def spacesEtaleLocalizationIsoInv (f : X ⟶ Y) [Etale f] :
    RingedSiteMap ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
      ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f))
      (spacesEtaleTopology X) (spacesStructureSheaf X) where
  base := spacesEtaleLocalizationFunctor f
  isMorphismOfSites := spacesEtaleLocalizationFunctor.instIsMorphismOfSites f
  structureSheafMap := spacesEtaleLocalizationIsoInvStructureSheaf f

/-- The forward localization map followed by the inverse is the identity on the domain site. -/
theorem spacesEtaleLocalizationIso_hom_inv_id (f : X ⟶ Y) [Etale f] :
    RingedSiteMap.comp (spacesEtaleLocalizationIsoHom f) (spacesEtaleLocalizationIsoInv f) =
      RingedSiteMap.id (spacesEtaleTopology X) (spacesStructureSheaf X) :=
  sorry

/-- The inverse localization map followed by the forward is the identity on the slice site. -/
theorem spacesEtaleLocalizationIso_inv_hom_id (f : X ⟶ Y) [Etale f] :
    RingedSiteMap.comp (spacesEtaleLocalizationIsoInv f) (spacesEtaleLocalizationIsoHom f) =
      RingedSiteMap.id ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
        ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) :=
  sorry

/-- Identification of spaces-étale ringed sites
`(X_spaces,étale, 𝒪_X) ≅ (Y_spaces,étale / X, 𝒪_Y restricted)` along an étale morphism of
algebraic spaces. -/
@[expose]
def spacesEtaleLocalizationIso (f : X ⟶ Y) [Etale f] :
    RingedSiteMap.Iso (spacesEtaleTopology X) (spacesStructureSheaf X)
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk f))
      ((spacesStructureSheaf Y).over (spacesEtaleSite.mk f)) where
  hom := spacesEtaleLocalizationIsoHom f
  inv := spacesEtaleLocalizationIsoInv f
  hom_inv_id := spacesEtaleLocalizationIso_hom_inv_id f
  inv_hom_id := spacesEtaleLocalizationIso_inv_hom_id f

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
