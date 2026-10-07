module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.Representable.Presentation
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import stacks_project.Chap96.Lemma_96_6_2_RingedTopos

/-!
# Ringed-topos presentations of the 96.8.1 identification and of scheme morphisms

A representing equivalence `𝒳 ≌ slice X` induces a morphism of ringed topoi
`(Sh(𝒳_τ), 𝒪_𝒳) ⟶ (Sh((Sch/X.left)_τ), 𝒪)`, obtained by composing the
associated morphism of ringed topoi of the equivalence with the iterated-slice
identification. A morphism of schemes likewise induces a cocontinuous morphism
of ringed topoi of big `τ`-sites, presenting `pullbackRingedHom`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory MorphismOfTopoiIn
open Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Ring-valued sheaves on a standard big `τ`-site compose with `forget RingCat`. -/
instance ringedSite_hasSheafCompose (τ : StandardTopology) (S : Scheme.{u}) :
    (ringedSite τ S).siteTopology.HasSheafCompose (forget RingCat.{u}) :=
  sorry

section RingedToposHom

variable (τ : StandardTopology) {T S : Scheme.{u}} (f : T ⟶ S)
variable [HasSheafify (τ.overTopology T) (Type u)]
variable [∀ P : (Over T)ᵒᵖ ⥤ Type u, (Over.map f).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over T)ᵒᵖ ⥤ RingCat.{u}, (Over.map f).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (Over.map f).op]

/-- Inverse-image comparison `(Over.map f)⁻¹ 𝒪_S ⟶ 𝒪_T` on global sections, induced by
`Over.mapForget f`. -/
def ringedToposHom_inverseImageStructureMap :
    ((Over.map f).sheafPushforwardContinuous RingCat.{u}
        (τ.overTopology T) (τ.overTopology S)).obj
      (ringedSite τ S).structureSheaf ⟶
      (ringedSite τ T).structureSheaf :=
  ⟨Scheme.Site.inverseStructurePresheafMap
    (Over.forget T) (Over.forget S) (Over.map f) (Over.mapForget f).inv⟩

/-- Direct-image form of the structure-sheaf map of `ringedToposHom`. -/
def ringedToposHom_structureMap :
    (ringedSite τ S).structureSheaf ⟶
      ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
        (τ.overTopology T) (τ.overTopology S)).obj
        (ringedSite τ T).structureSheaf :=
  ((Over.map f).sheafAdjunctionCocontinuous RingCat.{u}
      (τ.overTopology T) (τ.overTopology S)).homEquiv _ _
    (ringedToposHom_inverseImageStructureMap τ f)

/-- The morphism of topoi underlying `ringedToposHom τ f`. -/
def ringedToposHom_toToposVal :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (τ.overTopology S) (τ.overTopology T) :=
  (Over.map f).morphismOfTopoiInOfCocontinuous
    (τ.overTopology T) (τ.overTopology S)

/-- Forgetting rings commutes with the cocontinuous direct image along `Over.map f`. -/
def ringedToposHom_forgetIso :
    ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
          (τ.overTopology T) (τ.overTopology S)) ⋙
        sheafCompose (τ.overTopology S) (forget RingCat.{u}) ≅
      sheafCompose (τ.overTopology T) (forget RingCat.{u}) ⋙
        (ringedToposHom_toToposVal τ f).pushforward :=
  CategoryTheory.Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (Over.map f) (forget RingCat.{u}) (τ.overTopology T) (τ.overTopology S)

/-- The direct-image structure map of `ringedToposHom` preserves internal-ring operations. -/
theorem ringedToposHom_isRingCompatible :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (ringedSite τ T) (ringedSite τ S) _ _
      (ringedToposHom_toToposVal τ f)
      ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
        (τ.overTopology T) (τ.overTopology S))
      (ringedToposHom_forgetIso τ f)
      (ringedToposHom_structureMap τ f) :=
  sorry

/-- The morphism of big `τ`-ringed topoi induced by a morphism of schemes, presented by
the cocontinuous functor `Over.map f`. The continuous site-level presentation of the same
geometric morphism is `pullbackRingedHom τ f`. -/
def ringedToposHom :
    RingedSite.ToposHom (ringedSite τ T) (ringedSite τ S) :=
  @RingedSite.ToposHom.ofDirectImage (ringedSite τ T) (ringedSite τ S) _ _
    (ringedToposHom_toToposVal τ f)
    ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
      (τ.overTopology T) (τ.overTopology S))
    (ringedToposHom_forgetIso τ f)
    (ringedToposHom_structureMap τ f)
    (ringedToposHom_isRingCompatible τ f)

/-- The underlying morphism of topoi of `ringedToposHom τ f` is the cocontinuous
morphism of topoi induced by `Over.map f`. -/
theorem ringedToposHom_toTopos :
    (ringedToposHom τ f).toTopos = ringedToposHom_toToposVal τ f :=
  sorry

/-- The inverse-image structure map of `ringedToposHom τ f` is the mate of
`ringedToposHom_structureMap`. -/
theorem ringedToposHom_structureMap_eq :
    (ringedToposHom τ f).structureMap =
      @RingedSite.ToposHom.Direct.inverseStructureMap
        (ringedSite τ T) (ringedSite τ S) _ _
        (ringedToposHom_toToposVal τ f)
        ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
          (τ.overTopology T) (τ.overTopology S))
        (ringedToposHom_forgetIso τ f)
        (ringedToposHom_structureMap τ f)
        (ringedToposHom_isRingCompatible τ f) :=
  sorry

end RingedToposHom

end AlgebraicGeometry.StandardTopology.Big

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

/-- Pointwise right Kan extensions along `X.iteratedSliceForward` on `Over X`. -/
instance iteratedSliceForward_over_op_hasPointwiseRightKanExtension
    (X : Over S) (τ : StandardTopology)
    [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
        X.iteratedSliceForward.op.HasPointwiseRightKanExtension P] :
    ∀ P : (Over X)ᵒᵖ ⥤ Type u, X.iteratedSliceForward.op.HasPointwiseRightKanExtension P :=
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
    (associatedRingedSite_hasSheafCompose (slice X) τ)
    (StandardTopology.Big.ringedSite_hasSheafCompose τ X.left)
    (sliceAssociatedRingedToposHom_inverseImageStructureMap X τ).hom

/-- The underlying morphism of topoi of `sliceAssociatedRingedToposHom` is the
cocontinuous morphism of topoi of `X.iteratedSliceForward`. -/
theorem sliceAssociatedRingedToposHom_toTopos :
    (sliceAssociatedRingedToposHom X τ).toTopos =
      @RingedSite.Cocontinuous.toTopos.{u + 1, u, u + 1, u, u}
        (associatedRingedSite (slice X) τ)
        (StandardTopology.Big.ringedSite τ X.left) X.iteratedSliceForward
        (iteratedSliceForward_isCocontinuous X τ) ‹_› ‹_› :=
  sorry

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

/-- The identification of Lemma 96.8.1 as a morphism of ringed topoi
`(Sh(𝒳_τ), 𝒪_𝒳) ⟶ (Sh((Sch/X.left)_τ), 𝒪)`, obtained by composing
`associatedRingedToposHom e.hom τ` with `sliceAssociatedRingedToposHom X τ`. -/
def associatedRingedSiteToposHom :
    RingedSite.ToposHom (associatedRingedSite 𝒳 τ)
      (StandardTopology.Big.ringedSite τ X.left) :=
  @RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u}
    (associatedRingedSite 𝒳 τ) (associatedRingedSite (slice X) τ)
    (StandardTopology.Big.ringedSite τ X.left)
    (associatedRingedSite_hasSheafCompose 𝒳 τ)
    (associatedRingedSite_hasSheafCompose (slice X) τ)
    (StandardTopology.Big.ringedSite_hasSheafCompose τ X.left)
    (associatedRingedSiteEquivToposHom e τ)
    (sliceAssociatedRingedToposHom X τ)

/-- `associatedRingedSiteToposHom e τ` is the composite of the associated morphism of
ringed topoi of `e.hom` with the iterated-slice identification. -/
theorem associatedRingedSiteToposHom_eq :
    associatedRingedSiteToposHom e τ =
      RingedSite.ToposHom.comp (associatedRingedToposHom e.hom τ)
        (sliceAssociatedRingedToposHom X τ) :=
  sorry

/-- The underlying morphism of topoi of `associatedRingedSiteToposHom e τ` is the
composite of the associated morphism of topoi of `e.hom` with the iterated-slice
morphism of topoi. -/
theorem associatedRingedSiteToposHom_toTopos :
    (associatedRingedSiteToposHom e τ).toTopos =
      MorphismOfTopoiIn.comp (sliceAssociatedRingedToposHom X τ).toTopos
        (associatedRingedToposHom e.hom τ).toTopos :=
  sorry

end Identification

section RecoverTriangle

variable {𝒳 𝒴 : GroupoidsOver S} {X Y : Over S}

/-- A morphism of slice fibrations is `2`-isomorphic to the canonical `overMap` of its
terminal-object evaluation. Objectwise the comparison is the identity on the underlying
object of `Over S`. -/
def recoverSliceIso (G : slice X ⟶ slice Y) :
    G ≅ overMap (slice.eval G) :=
  InducedBicategory.isoMk
    (BasedNatIso.ofComponents
      (fun a ↦ Over.isoMk ((commIso G).app a) sorry) sorry sorry)

/-- The unit/counit triangle relating `f ≫ eY.hom` to the presentation of `f` through
`eX`. -/
def recoverUnitIso (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y) (f : 𝒳 ⟶ 𝒴) :
    (f ≫ eY.hom) ≅ eX.hom ≫ ((eX.inv ≫ f) ≫ eY.hom) :=
  (λ_ (f ≫ eY.hom)).symm ≪≫
    whiskerRightIso eX.unit (f ≫ eY.hom) ≪≫
    α_ eX.hom eX.inv (f ≫ eY.hom) ≪≫
    whiskerLeftIso eX.hom (α_ eX.inv f eY.hom).symm

/-- The recover triangle: `f ≫ eY.hom` is `2`-isomorphic to
`eX.hom ≫ overMap (Presentation.recover eX eY f)`. -/
def recoverTriangle (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y) (f : 𝒳 ⟶ 𝒴) :
    (f ≫ eY.hom) ≅ eX.hom ≫ overMap (Presentation.recover eX eY f) :=
  recoverUnitIso eX eY f ≪≫ whiskerLeftIso eX.hom (recoverSliceIso _)

/-- The total-functor form of `recoverTriangle`. -/
def recoverTriangle_toFunctor (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y)
    (f : 𝒳 ⟶ 𝒴) :
    toFunctor (f ≫ eY.hom) ≅
      toFunctor (eX.hom ≫ overMap (Presentation.recover eX eY f)) :=
  toFunctorIso (recoverTriangle eX eY f)

end RecoverTriangle

section AssociatedCocontinuity

variable {𝒳 𝒴 : GroupoidsOver S}

/-- `toFunctor h` is cocontinuous on the associated ringed-site topologies. -/
instance toFunctor_associatedRingedSite_isCocontinuous
    (h : 𝒳 ⟶ 𝒴) (τ : StandardTopology) :
    (toFunctor h).IsCocontinuous
      (associatedRingedSite 𝒳 τ).siteTopology
      (associatedRingedSite 𝒴 τ).siteTopology :=
  toFunctor_isCocontinuous h τ

end AssociatedCocontinuity

section OverMapCocontinuity

variable {X Y : Over S}

/-- `Over.map g` is cocontinuous on the associated ringed-site topologies of the
slices. -/
instance overMap_associatedRingedSite_isCocontinuous
    (g : X ⟶ Y) (τ : StandardTopology) :
    (Over.map g).IsCocontinuous
      (associatedRingedSite (slice X) τ).siteTopology
      (associatedRingedSite (slice Y) τ).siteTopology :=
  sorry

/-- Pointwise right Kan extensions along `Over.map g` on the associated ringed site of
`slice X`. -/
instance overMap_associatedRingedSite_op_hasPointwiseRightKanExtension
    (g : X ⟶ Y) (τ : StandardTopology) :
    ∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
      (Over.map g).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `Over.map g` on `Over X`. -/
instance overMap_over_op_hasPointwiseRightKanExtension (g : X ⟶ Y) :
    ∀ P : (Over X)ᵒᵖ ⥤ Type u, (Over.map g).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Iterated-slice followed by `Over.map g.left` is cocontinuous on the associated and big
`τ`-sites. -/
instance iteratedSliceForward_comp_map_isCocontinuous
    (g : X ⟶ Y) (τ : StandardTopology) :
    (X.iteratedSliceForward ⋙ Over.map g.left).IsCocontinuous
      (associatedRingedSite (slice X) τ).siteTopology (τ.overTopology Y.left) :=
  -- Local instance justification (search instability): `associatedRingedSite` is a def, so
  -- `siteTopology` does not fire the `associatedTopology` cocontinuity instances.
  letI := iteratedSliceForward_isCocontinuous X τ
  letI := AlgebraicGeometry.StandardTopology.Big.map_isCocontinuous τ g.left
  isCocontinuous_comp X.iteratedSliceForward (Over.map g.left)
    (associatedRingedSite (slice X) τ).siteTopology (τ.overTopology X.left)

/-- The total functor of `overMap g` is `Over.map g`, as an identity comparison of
functors `Over X ⥤ Over Y`. -/
def overMap_toFunctorIso (g : X ⟶ Y) :
    toFunctor (overMap g) ≅ Over.map g :=
  Iso.refl _

/-- The forward components of `overMap_toFunctorIso` are identities. -/
theorem overMap_toFunctorIso_hom_app (g : X ⟶ Y) (a : Over X) :
    (overMap_toFunctorIso g).hom.app a = 𝟙 ((Over.map g).obj a) :=
  sorry

/-- `Over.map g` followed by `Y.iteratedSliceForward` is cocontinuous from the associated
site of `slice X` to the big `τ`-site of `Y.left`. -/
instance overMap_comp_iteratedSliceForward_isCocontinuous
    (g : X ⟶ Y) (τ : StandardTopology) :
    (Over.map g ⋙ Y.iteratedSliceForward).IsCocontinuous
      (associatedRingedSite (slice X) τ).siteTopology (τ.overTopology Y.left) :=
  -- Local instance justification (search instability): `associatedRingedSite` is a def, so
  -- `siteTopology` does not fire the `associatedTopology` cocontinuity instances.
  letI := overMap_associatedRingedSite_isCocontinuous g τ
  letI := iteratedSliceForward_isCocontinuous Y τ
  isCocontinuous_comp (Over.map g) Y.iteratedSliceForward
    (associatedRingedSite (slice X) τ).siteTopology
    (associatedRingedSite (slice Y) τ).siteTopology

/-- Pointwise right Kan extensions along the opposite of
`X.iteratedSliceForward ⋙ Over.map g.left`. -/
instance iteratedSliceForward_comp_map_op_hasPointwiseRightKanExtension
    (g : X ⟶ Y) (τ : StandardTopology)
    [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
        X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
    [∀ P : (Over X.left)ᵒᵖ ⥤ Type u, (Over.map g.left).op.HasPointwiseRightKanExtension P] :
    ∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
      (X.iteratedSliceForward ⋙ Over.map g.left).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along
`X.iteratedSliceForward ⋙ Over.map g.left` on `Over X`. -/
instance iteratedSliceForward_comp_map_over_op_hasPointwiseRightKanExtension
    (g : X ⟶ Y)
    [∀ P : (Over X)ᵒᵖ ⥤ Type u, X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
    [∀ P : (Over X.left)ᵒᵖ ⥤ Type u, (Over.map g.left).op.HasPointwiseRightKanExtension P] :
    ∀ P : (Over X)ᵒᵖ ⥤ Type u,
      (X.iteratedSliceForward ⋙ Over.map g.left).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `Over.map g ⋙ Y.iteratedSliceForward` on `Over X`. -/
instance overMap_comp_iteratedSliceForward_op_hasPointwiseRightKanExtension
    (g : X ⟶ Y)
    [∀ P : (Over X)ᵒᵖ ⥤ Type u, (Over.map g).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over Y)ᵒᵖ ⥤ Type u, Y.iteratedSliceForward.op.HasPointwiseRightKanExtension P] :
    ∀ P : (Over X)ᵒᵖ ⥤ Type u,
      (Over.map g ⋙ Y.iteratedSliceForward).op.HasPointwiseRightKanExtension P :=
  sorry

end OverMapCocontinuity

section PushforwardHelpers

/-- Composite cocontinuous sheaf pushforwards, compared along an identification of the
composite functor. Cocontinuity is supplied as instance binders because
`associatedRingedSite` is a def, so typeclass search cannot recover it from
`siteTopology`. -/
def sheafPushforwardCocontinuousCompIso
    {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)} [Category.{u} D]
    {E : Type (u + 1)} [Category.{u} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    (F : C ⥤ D) (G : D ⥤ E) {FG : C ⥤ E} (e : F ⋙ G ≅ FG)
    [hF : F.IsCocontinuous J K] [hG : G.IsCocontinuous K L]
    [hFG : FG.IsCocontinuous J L]
    [kanF : ∀ P : Cᵒᵖ ⥤ Type u, F.op.HasPointwiseRightKanExtension P]
    [kanG : ∀ P : Dᵒᵖ ⥤ Type u, G.op.HasPointwiseRightKanExtension P]
    [kanFG : ∀ P : Cᵒᵖ ⥤ Type u, FG.op.HasPointwiseRightKanExtension P] :
    F.sheafPushforwardCocontinuous (Type u) J K ⋙
      G.sheafPushforwardCocontinuous (Type u) K L ≅
        FG.sheafPushforwardCocontinuous (Type u) J L :=
  -- Local instance justification (search instability): topologies are fields of defs.
  letI := hF
  letI := hG
  letI := hFG
  letI := kanF
  letI := kanG
  letI := kanFG
  sheafPushforwardCocontinuousComp' (A := Type u) J K L F G e

/-- A natural isomorphism of cocontinuous functors induces an isomorphism of sheaf
pushforwards. Cocontinuity is supplied as instance binders because
`associatedRingedSite` is a def. -/
def sheafPushforwardCocontinuousNatIso
    {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)} [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {F F' : C ⥤ D} (e : F ≅ F')
    [hF : F.IsCocontinuous J K] [hF' : F'.IsCocontinuous J K]
    [kanF : ∀ P : Cᵒᵖ ⥤ Type u, F.op.HasPointwiseRightKanExtension P]
    [kanF' : ∀ P : Cᵒᵖ ⥤ Type u, F'.op.HasPointwiseRightKanExtension P] :
    F.sheafPushforwardCocontinuous (Type u) J K ≅
      F'.sheafPushforwardCocontinuous (Type u) J K :=
  -- Local instance justification (search instability): topologies are fields of defs.
  letI := hF
  letI := hF'
  letI := kanF
  letI := kanF'
  sheafPushforwardCocontinuousIso (A := Type u) (J := J) (K := K) (u := F) e

end PushforwardHelpers

section IteratedPushforwardIso

variable {X Y : Over S}

/-- Direct-image comparison of `Over.map g` then `Y.iteratedSliceForward` with
`X.iteratedSliceForward` then `Over.map g.left`. -/
def iteratedSliceForward_pushforwardIso (g : X ⟶ Y) (τ : StandardTopology)
    [HasSheafify (associatedRingedSite (slice X) τ).siteTopology (Type u)]
    [HasSheafify (associatedRingedSite (slice Y) τ).siteTopology (Type u)]
    [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
        X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
    [∀ P : (associatedRingedSite (slice Y) τ).carrierᵒᵖ ⥤ Type u,
        Y.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
    [∀ P : (Over X.left)ᵒᵖ ⥤ Type u, (Over.map g.left).op.HasPointwiseRightKanExtension P]
    [hg : (Over.map g).IsCocontinuous
        (associatedRingedSite (slice X) τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology]
    [hX : X.iteratedSliceForward.IsCocontinuous
        (associatedRingedSite (slice X) τ).siteTopology (τ.overTopology X.left)]
    [hY : Y.iteratedSliceForward.IsCocontinuous
        (associatedRingedSite (slice Y) τ).siteTopology (τ.overTopology Y.left)]
    [hleft : (Over.map g.left).IsCocontinuous (τ.overTopology X.left) (τ.overTopology Y.left)]
    [hcomp : (X.iteratedSliceForward ⋙ Over.map g.left).IsCocontinuous
        (associatedRingedSite (slice X) τ).siteTopology (τ.overTopology Y.left)] :
    (Over.map g).sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite (slice X) τ).siteTopology
          (associatedRingedSite (slice Y) τ).siteTopology ⋙
        Y.iteratedSliceForward.sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite (slice Y) τ).siteTopology (τ.overTopology Y.left) ≅
      X.iteratedSliceForward.sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite (slice X) τ).siteTopology (τ.overTopology X.left) ⋙
        (Over.map g.left).sheafPushforwardCocontinuous (Type u)
          (τ.overTopology X.left) (τ.overTopology Y.left) :=
  sheafPushforwardCocontinuousCompIso
      (associatedRingedSite (slice X) τ).siteTopology
      (associatedRingedSite (slice Y) τ).siteTopology (τ.overTopology Y.left)
      (Over.map g) Y.iteratedSliceForward (Over.iteratedSliceForwardNaturalityIso g).symm
      (hF := hg) (hG := hY) (hFG := hcomp)
      (kanF := overMap_over_op_hasPointwiseRightKanExtension g)
      (kanG := iteratedSliceForward_over_op_hasPointwiseRightKanExtension Y τ)
      (kanFG := iteratedSliceForward_comp_map_over_op_hasPointwiseRightKanExtension g) ≪≫
    (sheafPushforwardCocontinuousCompIso
        (associatedRingedSite (slice X) τ).siteTopology (τ.overTopology X.left)
        (τ.overTopology Y.left) X.iteratedSliceForward (Over.map g.left)
        (Iso.refl _)
        (hF := hX) (hG := hleft) (hFG := hcomp)
        (kanF := iteratedSliceForward_over_op_hasPointwiseRightKanExtension X τ)
        (kanFG := iteratedSliceForward_comp_map_over_op_hasPointwiseRightKanExtension g)).symm

end IteratedPushforwardIso

section CompHomIso

variable {𝒳 𝒴 : GroupoidsOver S} {X Y : Over S}

/-- Direct images along `toFunctor f` and `toFunctor eY.hom` identify with the direct image
along `toFunctor (f ≫ eY.hom)`. -/
def associatedRingedToposHom_comp_upperIso
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
        (Over.map (Presentation.recover eX eY f).left).op]
    [hf : (toFunctor f).IsCocontinuous
        (associatedRingedSite 𝒳 τ).siteTopology (associatedRingedSite 𝒴 τ).siteTopology]
    [heY : (toFunctor eY.hom).IsCocontinuous
        (associatedRingedSite 𝒴 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology]
    [hfY : (toFunctor (f ≫ eY.hom)).IsCocontinuous
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology] :
    (toFunctor f).sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite 𝒳 τ).siteTopology
          (associatedRingedSite 𝒴 τ).siteTopology ⋙
        (toFunctor eY.hom).sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite 𝒴 τ).siteTopology
          (associatedRingedSite (slice Y) τ).siteTopology ≅
      (toFunctor (f ≫ eY.hom)).sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology :=
  sheafPushforwardCocontinuousCompIso
    (associatedRingedSite 𝒳 τ).siteTopology (associatedRingedSite 𝒴 τ).siteTopology
    (associatedRingedSite (slice Y) τ).siteTopology (toFunctor f) (toFunctor eY.hom)
    (ObjectProperty.FullSubbicategory.toFunctor.compIso f eY.hom)
    (hF := hf) (hG := heY) (hFG := hfY)
    (kanF := toFunctor_op_hasPointwiseRightKanExtension_type f τ)
    (kanG := toFunctor_op_hasPointwiseRightKanExtension_type eY.hom τ)
    (kanFG := toFunctor_op_hasPointwiseRightKanExtension_type (f ≫ eY.hom) τ)

/-- Direct images along `toFunctor eX.hom` and `Over.map (recover eX eY f)` identify with
the direct image along their composite. -/
def associatedRingedToposHom_comp_lowerMidIso
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
        (Over.map (Presentation.recover eX eY f).left).op]
    [heX : (toFunctor eX.hom).IsCocontinuous
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice X) τ).siteTopology]
    [hmap : (Over.map (Presentation.recover eX eY f)).IsCocontinuous
        (associatedRingedSite (slice X) τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology]
    [hcomp : (toFunctor (eX.hom ≫ overMap (Presentation.recover eX eY f))).IsCocontinuous
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology] :
    (toFunctor eX.hom).sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite 𝒳 τ).siteTopology
          (associatedRingedSite (slice X) τ).siteTopology ⋙
        (Over.map (Presentation.recover eX eY f)).sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite (slice X) τ).siteTopology
          (associatedRingedSite (slice Y) τ).siteTopology ≅
      (toFunctor (eX.hom ≫ overMap (Presentation.recover eX eY f))).sheafPushforwardCocontinuous
        (Type u) (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology :=
  sheafPushforwardCocontinuousCompIso
    (associatedRingedSite 𝒳 τ).siteTopology
    (associatedRingedSite (slice X) τ).siteTopology
    (associatedRingedSite (slice Y) τ).siteTopology (toFunctor eX.hom)
    (Over.map (Presentation.recover eX eY f))
    (isoWhiskerLeft (toFunctor eX.hom)
        (overMap_toFunctorIso (Presentation.recover eX eY f)).symm ≪≫
      ObjectProperty.FullSubbicategory.toFunctor.compIso eX.hom
        (overMap (Presentation.recover eX eY f)))
    (hF := heX) (hG := hmap) (hFG := hcomp)
    (kanF := toFunctor_op_hasPointwiseRightKanExtension_type eX.hom τ)
    (kanG := overMap_associatedRingedSite_op_hasPointwiseRightKanExtension
      (Presentation.recover eX eY f) τ)
    (kanFG := toFunctor_op_hasPointwiseRightKanExtension_type
      (eX.hom ≫ overMap (Presentation.recover eX eY f)) τ)

/-- Direct images along `toFunctor (f ≫ eY.hom)` and
`toFunctor (eX.hom ≫ overMap (recover eX eY f))` identify via `recoverTriangle`. -/
def associatedRingedToposHom_comp_siteIso
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
        (Over.map (Presentation.recover eX eY f).left).op]
    [hfY : (toFunctor (f ≫ eY.hom)).IsCocontinuous
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology]
    [hrec : (toFunctor (eX.hom ≫ overMap (Presentation.recover eX eY f))).IsCocontinuous
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology] :
    (toFunctor (f ≫ eY.hom)).sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology ≅
      (toFunctor (eX.hom ≫ overMap (Presentation.recover eX eY f))).sheafPushforwardCocontinuous
        (Type u) (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology :=
  sheafPushforwardCocontinuousNatIso
    (associatedRingedSite 𝒳 τ).siteTopology
    (associatedRingedSite (slice Y) τ).siteTopology
    (recoverTriangle_toFunctor eX eY f)
    (hF := hfY) (hF' := hrec)
    (kanF := toFunctor_op_hasPointwiseRightKanExtension_type (f ≫ eY.hom) τ)
    (kanF' := toFunctor_op_hasPointwiseRightKanExtension_type
      (eX.hom ≫ overMap (Presentation.recover eX eY f)) τ)

/-- The invertible `2`-cell of Lemma 96.8.2, as an isomorphism of type-valued direct images. -/
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
  -- Local instance justification (search instability): `associatedRingedSite` is a def, so
  -- `siteTopology` does not fire the `associatedTopology` cocontinuity instances.
  letI := toFunctor_isCocontinuous f τ
  letI := toFunctor_isCocontinuous eX.hom τ
  letI := toFunctor_isCocontinuous eY.hom τ
  letI := toFunctor_isCocontinuous (f ≫ eY.hom) τ
  letI := toFunctor_isCocontinuous (eX.hom ≫ overMap (Presentation.recover eX eY f)) τ
  letI := overMap_associatedRingedSite_isCocontinuous (Presentation.recover eX eY f) τ
  letI := iteratedSliceForward_isCocontinuous X τ
  letI := iteratedSliceForward_isCocontinuous Y τ
  letI := AlgebraicGeometry.StandardTopology.Big.map_isCocontinuous τ
    (Presentation.recover eX eY f).left
  letI := iteratedSliceForward_comp_map_isCocontinuous (Presentation.recover eX eY f) τ
  letI := overMap_comp_iteratedSliceForward_isCocontinuous (Presentation.recover eX eY f) τ
  letI := toFunctor_op_hasPointwiseRightKanExtension_total (f ≫ eY.hom)
  letI := toFunctor_op_hasPointwiseRightKanExtension_total
    (eX.hom ≫ overMap (Presentation.recover eX eY f))
  letI := overMap_associatedRingedSite_op_hasPointwiseRightKanExtension
    (Presentation.recover eX eY f) τ
  (associator
      ((toFunctor f).sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite 𝒴 τ).siteTopology)
      ((toFunctor eY.hom).sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite 𝒴 τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology)
      (Y.iteratedSliceForward.sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite (slice Y) τ).siteTopology (τ.overTopology Y.left))).symm ≪≫
    isoWhiskerRight (associatedRingedToposHom_comp_upperIso eX eY f τ)
      (Y.iteratedSliceForward.sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite (slice Y) τ).siteTopology (τ.overTopology Y.left)) ≪≫
    isoWhiskerRight (associatedRingedToposHom_comp_siteIso eX eY f τ)
      (Y.iteratedSliceForward.sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite (slice Y) τ).siteTopology (τ.overTopology Y.left)) ≪≫
    isoWhiskerRight (associatedRingedToposHom_comp_lowerMidIso eX eY f τ).symm
      (Y.iteratedSliceForward.sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite (slice Y) τ).siteTopology (τ.overTopology Y.left)) ≪≫
    associator
      ((toFunctor eX.hom).sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice X) τ).siteTopology)
      ((Over.map (Presentation.recover eX eY f)).sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite (slice X) τ).siteTopology
        (associatedRingedSite (slice Y) τ).siteTopology)
      (Y.iteratedSliceForward.sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite (slice Y) τ).siteTopology (τ.overTopology Y.left)) ≪≫
    isoWhiskerLeft
      ((toFunctor eX.hom).sheafPushforwardCocontinuous (Type u)
        (associatedRingedSite 𝒳 τ).siteTopology
        (associatedRingedSite (slice X) τ).siteTopology)
      (iteratedSliceForward_pushforwardIso (Presentation.recover eX eY f) τ) ≪≫
    (associator
        ((toFunctor eX.hom).sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite 𝒳 τ).siteTopology
          (associatedRingedSite (slice X) τ).siteTopology)
        (X.iteratedSliceForward.sheafPushforwardCocontinuous (Type u)
          (associatedRingedSite (slice X) τ).siteTopology (τ.overTopology X.left))
        ((Over.map (Presentation.recover eX eY f).left).sheafPushforwardCocontinuous (Type u)
          (τ.overTopology X.left) (τ.overTopology Y.left))).symm

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


end AlgebraicGeometry.GroupoidsOver
