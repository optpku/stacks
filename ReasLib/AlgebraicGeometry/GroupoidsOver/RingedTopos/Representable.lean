module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.RingedTopos
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import ReasLib.CategoryTheory.Fibered.Representable.Comparison

@[expose] public section
open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory MorphismOfTopoiIn
open Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The iterated-slice functor `Over X ⥤ Over X.left` is cocontinuous from the associated
`τ`-site of `slice X` to the big `τ`-site of `X.left`. -/
instance iteratedSliceForward_isCocontinuous (X : Over S) (τ : StandardTopology) :
    X.iteratedSliceForward.IsCocontinuous
      (associatedRingedSite (slice X) τ).siteTopology
      (StandardTopology.Big.ringedSite τ X.left).siteTopology :=
  sorry

/-- The iterated-slice functor `Over X ⥤ Over X.left` is continuous from the associated
`τ`-site of `slice X` to the big `τ`-site of `X.left`. -/
instance iteratedSliceForward_isContinuous (X : Over S) (τ : StandardTopology) :
    X.iteratedSliceForward.IsContinuous
      (associatedRingedSite (slice X) τ).siteTopology
      (StandardTopology.Big.ringedSite τ X.left).siteTopology :=
  sorry

/-- Inverse-image comparison `iteratedSliceForward⁻¹ 𝒪_{X.left} ⟶ 𝒪_{slice X}` on global
sections, using the identity realization `iteratedSliceForward ⋙ Over.forget X.left =
(slice X).p ⋙ Over.forget S`. -/
def sliceAssociatedRingedToposHom_inverseImageStructureMap (X : Over S)
    (τ : StandardTopology) :
    (X.iteratedSliceForward.sheafPushforwardContinuous RingCat.{u}
        (associatedRingedSite (slice X) τ).siteTopology
        (StandardTopology.Big.ringedSite τ X.left).siteTopology).obj
      (StandardTopology.Big.ringedSite τ X.left).structureSheaf ⟶
      (associatedRingedSite (slice X) τ).structureSheaf :=
  ⟨Scheme.Site.inverseStructurePresheafMap
    ((slice X).p ⋙ Over.forget S) (Over.forget X.left) X.iteratedSliceForward (𝟙 _)⟩

section SliceAssociated

variable (X : Over S) (τ : StandardTopology)
variable [HasSheafify (associatedRingedSite (slice X) τ).siteTopology (Type u)]
variable [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
    X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]

/-- The morphism of ringed topoi `(Sh((slice X)_τ), 𝒪) ⟶ (Sh((Sch/X.left)_τ), 𝒪)`
presented by the cocontinuous iterated-slice functor `X.iteratedSliceForward`. -/
def sliceAssociatedRingedToposHom :
    RingedSite.ToposHom (associatedRingedSite (slice X) τ)
      (StandardTopology.Big.ringedSite τ X.left) :=
  @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u}
    (associatedRingedSite (slice X) τ)
    (StandardTopology.Big.ringedSite τ X.left) X.iteratedSliceForward
    (iteratedSliceForward_isCocontinuous X τ) ‹_› ‹_›
    (associatedTopology_hasSheafCompose (slice X) τ)
    (StandardTopology.Big.overTopology_hasSheafCompose_ring τ X.left)
    (sliceAssociatedRingedToposHom_inverseImageStructureMap X τ).hom

/-- The underlying morphism of topoi of `sliceAssociatedRingedToposHom` is the
cocontinuous morphism of topoi of `X.iteratedSliceForward`. -/
theorem sliceAssociatedRingedToposHom_toTopos :
    (sliceAssociatedRingedToposHom X τ).toTopos =
      @RingedSite.Cocontinuous.toTopos.{u + 1, u, u + 1, u, u}
        (associatedRingedSite (slice X) τ)
        (StandardTopology.Big.ringedSite τ X.left) X.iteratedSliceForward
        (iteratedSliceForward_isCocontinuous X τ) ‹_› ‹_› :=
  rfl

end SliceAssociated

section Identification

variable {𝒳 : GroupoidsOver S} {X : Over S} (e : 𝒳 ≌ slice X) (τ : StandardTopology)
variable [HasSheafify (associatedRingedSite 𝒳 τ).siteTopology (Type u)]
variable [HasSheafify (associatedRingedSite (slice X) τ).siteTopology (Type u)]
variable [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor e.hom).op.HasPointwiseRightKanExtension P]
variable [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
    X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]

/-- The associated morphism of ringed topoi of a representing equivalence `e`. -/
def associatedRingedSiteEquivToposHom :
    RingedSite.ToposHom (associatedRingedSite 𝒳 τ)
      (associatedRingedSite (slice X) τ) :=
  associatedRingedToposHom e.hom τ

/-- A representing equivalence induces a morphism of ringed topoi
`(Sh(𝒳_τ), 𝒪_𝒳) ⟶ (Sh((Sch/X.left)_τ), 𝒪)`, obtained by composing
`associatedRingedToposHom e.hom τ` with `sliceAssociatedRingedToposHom X τ`. -/
def associatedRingedSiteToposHom :
    RingedSite.ToposHom (associatedRingedSite 𝒳 τ)
      (StandardTopology.Big.ringedSite τ X.left) :=
  @RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u}
    (associatedRingedSite 𝒳 τ) (associatedRingedSite (slice X) τ)
    (StandardTopology.Big.ringedSite τ X.left)
    (associatedTopology_hasSheafCompose 𝒳 τ)
    (associatedTopology_hasSheafCompose (slice X) τ)
    (StandardTopology.Big.overTopology_hasSheafCompose_ring τ X.left)
    (associatedRingedSiteEquivToposHom e τ)
    (sliceAssociatedRingedToposHom X τ)

/-- `associatedRingedSiteToposHom e τ` is the composite of the associated morphism of
ringed topoi of `e.hom` with the iterated-slice identification. -/
theorem associatedRingedSiteToposHom_eq :
    associatedRingedSiteToposHom e τ =
      RingedSite.ToposHom.comp (associatedRingedToposHom e.hom τ)
        (sliceAssociatedRingedToposHom X τ) :=
  rfl

/-- The underlying morphism of topoi of `associatedRingedSiteToposHom e τ` is the
composite of the associated morphism of topoi of `e.hom` with the iterated-slice
morphism of topoi. -/
theorem associatedRingedSiteToposHom_toTopos :
    (associatedRingedSiteToposHom e τ).toTopos =
      MorphismOfTopoiIn.comp (sliceAssociatedRingedToposHom X τ).toTopos
        (associatedRingedToposHom e.hom τ).toTopos :=
  rfl

end Identification

section CompHomIso
variable {𝒳 𝒴 : GroupoidsOver S} {X Y : Over S}

/-- Direct images commute with the recovered morphism through chosen slice presentations. -/
def associatedRingedToposHom_comp_homIso
    (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y) (f : 𝒳 ⟶ 𝒴) (τ : StandardTopology)
    [HasSheafify (associatedRingedSite 𝒳 τ).siteTopology (Type u)]
    [HasSheafify (associatedRingedSite 𝒴 τ).siteTopology (Type u)]
    [HasSheafify (associatedRingedSite (slice X) τ).siteTopology (Type u)]
    [HasSheafify (associatedRingedSite (slice Y) τ).siteTopology (Type u)]
    [HasSheafify (τ.overTopology X.left) (Type u)]
    [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor eX.hom).op.HasPointwiseRightKanExtension P]
    [∀ P : 𝒴.totalᵒᵖ ⥤ Type u, (toFunctor eY.hom).op.HasPointwiseRightKanExtension P]
    [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
        X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
    [∀ P : (associatedRingedSite (slice Y) τ).carrierᵒᵖ ⥤ Type u,
        Y.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
    [∀ P : (Over X.left)ᵒᵖ ⥤ Type u,
        (Over.map (Presentation.recover eX eY f).left).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over X.left)ᵒᵖ ⥤ RingCat.{u},
        (Over.map (Presentation.recover eX eY f).left).op.HasPointwiseRightKanExtension P]
    [(forget RingCat.{u}).PreservesRightKanExtensions
        (Over.map (Presentation.recover eX eY f).left).op] :
    (RingedSite.ToposHom.comp (associatedRingedToposHom f τ)
        (associatedRingedSiteToposHom eY τ)).toTopos.pushforward ≅
      (RingedSite.ToposHom.comp (associatedRingedSiteToposHom eX τ)
        (StandardTopology.Big.ringedToposHom τ
          (Presentation.recover eX eY f).left)).toTopos.pushforward :=

  let g := Presentation.recover eX eY f
  let fC := (toFunctor f).sheafPushforwardContinuous (Type u)
    (𝒳.associatedTopology τ) (𝒴.associatedTopology τ)
  let eXC := (toFunctor eX.hom).sheafPushforwardContinuous (Type u)
    (𝒳.associatedTopology τ) ((slice X).associatedTopology τ)
  let eYC := (toFunctor eY.hom).sheafPushforwardContinuous (Type u)
    (𝒴.associatedTopology τ) ((slice Y).associatedTopology τ)
  let xC := X.iteratedSliceForward.sheafPushforwardContinuous (Type u)
    ((slice X).associatedTopology τ) (τ.overTopology X.left)
  let yC := Y.iteratedSliceForward.sheafPushforwardContinuous (Type u)
    ((slice Y).associatedTopology τ) (τ.overTopology Y.left)
  let gC := (Over.map g.left).sheafPushforwardContinuous (Type u)
    (τ.overTopology X.left) (τ.overTopology Y.left)
  let totalIso :
      (toFunctor f ⋙ toFunctor eY.hom) ⋙ Y.iteratedSliceForward ≅
        (toFunctor eX.hom ⋙ X.iteratedSliceForward) ⋙ Over.map g.left :=
    isoWhiskerRight
      (ObjectProperty.FullSubbicategory.toFunctor.compIso f eY.hom ≪≫
        Presentation.triangleToFunctor eX eY f ≪≫
        (ObjectProperty.FullSubbicategory.toFunctor.compIso eX.hom (overMap g)).symm)
      Y.iteratedSliceForward ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (toFunctor eX.hom) (Over.iteratedSliceForwardNaturalityIso g).symm ≪≫
    (Functor.associator _ _ _).symm
  let continuousIso : yC ⋙ eYC ⋙ fC ≅ gC ⋙ xC ⋙ eXC :=
    Functor.fullyFaithfulCancelRight (sheafToPresheaf (𝒳.associatedTopology τ) (Type u))
      (isoWhiskerLeft (sheafToPresheaf (τ.overTopology Y.left) (Type u))
        ((whiskeringLeft _ _ (Type u)).mapIso (NatIso.op totalIso.symm)))
  let upperIso := isoWhiskerRight
    (isoWhiskerLeft yC
      (sheafificationNatIso (associatedRingedSite (slice Y) τ).siteTopology (Type u))).symm (eYC ⋙ fC)
  let lowerIso :=
    isoWhiskerRight
      (isoWhiskerLeft gC
        (sheafificationNatIso (τ.overTopology X.left) (Type u))).symm
      ((sliceAssociatedRingedToposHom X τ).toTopos.inverseImage ⋙ eXC) ≪≫
    isoWhiskerLeft gC
      (isoWhiskerRight
        (isoWhiskerLeft xC
          (sheafificationNatIso (associatedRingedSite (slice X) τ).siteTopology (Type u))).symm eXC)
  (((RingedSite.ToposHom.comp (associatedRingedToposHom f τ)
      (associatedRingedSiteToposHom eY τ)).toTopos.adjunction).ofNatIsoLeft
      (upperIso ≪≫ continuousIso ≪≫ lowerIso.symm)).rightAdjointUniq
    (RingedSite.ToposHom.comp (associatedRingedSiteToposHom eX τ)
      (StandardTopology.Big.ringedToposHom τ g.left)).toTopos.adjunction

/-- Compatibility of `associatedRingedToposHom_comp_homIso` with ring-valued direct-image
structure maps. -/
theorem associatedRingedToposHom_comp_homIso_comm
    (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y) (f : 𝒳 ⟶ 𝒴) (τ : StandardTopology)
    [HasSheafify (𝒳.associatedRingedSite τ).siteTopology (Type u)]
    [HasSheafify (𝒴.associatedRingedSite τ).siteTopology (Type u)]
    [HasSheafify ((slice X).associatedRingedSite τ).siteTopology (Type u)]
    [HasSheafify ((slice Y).associatedRingedSite τ).siteTopology (Type u)]
    [HasSheafify (τ.overTopology X.left) (Type u)]
    [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor eX.hom).op.HasPointwiseRightKanExtension P]
    [∀ P : 𝒴.totalᵒᵖ ⥤ Type u, (toFunctor eY.hom).op.HasPointwiseRightKanExtension P]
    [∀ P : ((slice X).associatedRingedSite τ).carrierᵒᵖ ⥤ Type u,
        X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
    [∀ P : ((slice Y).associatedRingedSite τ).carrierᵒᵖ ⥤ Type u,
        Y.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
    [∀ P : (Over X.left)ᵒᵖ ⥤ Type u,
        (Over.map (Presentation.recover eX eY f).left).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over X.left)ᵒᵖ ⥤ RingCat.{u},
        (Over.map (Presentation.recover eX eY f).left).op.HasPointwiseRightKanExtension P]
    [(forget RingCat.{u}).PreservesRightKanExtensions
        (Over.map (Presentation.recover eX eY f).left).op]
    :
    (RingedSite.ToposHom.comp (associatedRingedToposHom f τ)
            (associatedRingedSiteToposHom eY τ)).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (associatedRingedToposHom_comp_homIso eX eY f τ).hom).app
          (associatedRingedSite 𝒳 τ).structureSheaf =
      (RingedSite.ToposHom.comp (associatedRingedSiteToposHom eX τ)
          (StandardTopology.Big.ringedToposHom τ
            (Presentation.recover eX eY f).left)).directStructureMap :=
  sorry


end CompHomIso

variable {S : Scheme.{u}} {𝒳 𝒴 : GroupoidsOver S} {X Y : Over S}
variable (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y) (f : 𝒳 ⟶ 𝒴) (τ : StandardTopology)
variable [HasSheafify (associatedRingedSite 𝒳 τ).siteTopology (Type u)]
variable [HasSheafify (associatedRingedSite 𝒴 τ).siteTopology (Type u)]
variable [HasSheafify (associatedRingedSite (slice X) τ).siteTopology (Type u)]
variable [HasSheafify (associatedRingedSite (slice Y) τ).siteTopology (Type u)]
variable [HasSheafify (τ.overTopology X.left) (Type u)]
variable [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
variable [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor eX.hom).op.HasPointwiseRightKanExtension P]
variable [∀ P : 𝒴.totalᵒᵖ ⥤ Type u, (toFunctor eY.hom).op.HasPointwiseRightKanExtension P]
variable [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
    X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
variable [∀ P : (associatedRingedSite (slice Y) τ).carrierᵒᵖ ⥤ Type u,
    Y.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over X.left)ᵒᵖ ⥤ Type u,
    (Over.map (Presentation.recover eX eY f).left).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over X.left)ᵒᵖ ⥤ RingCat.{u},
    (Over.map (Presentation.recover eX eY f).left).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions
    (Over.map (Presentation.recover eX eY f).left).op]

/-- The ringed-topos square determined by presentations and the recovered base morphism. -/
def associatedRingedToposHom_comp :
    RingedSite.ToposHom.CommSquare
      (associatedRingedSite 𝒳 τ) (associatedRingedSite 𝒴 τ)
      (StandardTopology.Big.ringedSite τ X.left)
      (StandardTopology.Big.ringedSite τ Y.left) where
  upper := associatedRingedToposHom f τ
  left := associatedRingedSiteToposHom eX τ
  right := associatedRingedSiteToposHom eY τ
  lower := StandardTopology.Big.ringedToposHom τ
    (Presentation.recover eX eY f).left
  cell :=
    { homIso := associatedRingedToposHom_comp_homIso eX eY f τ
      comm := associatedRingedToposHom_comp_homIso_comm eX eY f τ }

/-- The upper edge of `associatedRingedToposHom_comp` is the associated morphism of
ringed topoi of `f`. -/
theorem associatedRingedToposHom_comp_upper :
    (associatedRingedToposHom_comp eX eY f τ).upper = associatedRingedToposHom f τ :=
  rfl

/-- The left edge of `associatedRingedToposHom_comp` is the representing identification
of `𝒳`. -/
theorem associatedRingedToposHom_comp_left :
    (associatedRingedToposHom_comp eX eY f τ).left =
      associatedRingedSiteToposHom eX τ :=
  rfl

/-- The right edge of `associatedRingedToposHom_comp` is the representing identification
of `𝒴`. -/
theorem associatedRingedToposHom_comp_right :
    (associatedRingedToposHom_comp eX eY f τ).right =
      associatedRingedSiteToposHom eY τ :=
  rfl

/-- The lower edge of `associatedRingedToposHom_comp` is the big-site morphism of
ringed topoi of the corresponding scheme morphism. -/
theorem associatedRingedToposHom_comp_lower :
    (associatedRingedToposHom_comp eX eY f τ).lower =
      StandardTopology.Big.ringedToposHom τ
        (Presentation.recover eX eY f).left :=
  rfl

/-- The stored `2`-cell of `associatedRingedToposHom_comp` is
`associatedRingedToposHom_comp_homIso`. -/
theorem associatedRingedToposHom_comp_homIso_eq :
    (associatedRingedToposHom_comp eX eY f τ).cell.homIso =
      associatedRingedToposHom_comp_homIso eX eY f τ :=
  rfl


end AlgebraicGeometry.GroupoidsOver
