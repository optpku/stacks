/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule
public import stacks_project.Chap65.Lemma_65_7_2_Pullback
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap96.Lemma_96_10_1_Comparison
public import stacks_project.Chap96.«96_10_3_1_Restriction»
public import stacks_project.Chap96.«96_10_3_1_Geometry»
public import stacks_project.Chap96.«96_10_3_3_RepresentedSections»
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Adjunction

/-!
# Big-versus-small étale pushforward comparison

For a morphism `f : F ⟶ G` of algebraic spaces, the restriction of the CFG
pushforward `f_* ℱ` to `G_étale` is canonically identified with the small étale
pushforward of the restriction of `ℱ` to `F_étale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite FiberedCategoryOver.Groupoids
open CategoryTheory.CategoryOfElements
open CategoryTheory.Sheaf.InternalModule
open Limits.Types
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The CFG étale pushforward of a sheaf with successor-universe coefficients.
Each actual comma diagram already has coefficients and indices in this universe. -/
abbrev etalePushforward {F G : AlgebraicSpace S} (f : F ⟶ G) :
    Sheaf F.toGroupoids.etaleTopology (Type (u + 1)) ⥤
      Sheaf G.toGroupoids.etaleTopology (Type (u + 1)) :=
  (toFunctor (toGroupoids.map f)).sheafPushforwardOfSmallSections.{u + 1, u, u + 1, u, u + 1}
    F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology

section CompareTypeSucc

variable {F G : AlgebraicSpace S} (f : F ⟶ G)
variable (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1)))

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category. -/
def compareLimitHom (V : smallEtaleSite G) :
    limit (compareBigDiag f ℱ V) ⟶ limit (compareSmallDiag f ℱ V) :=
  limit.pre (compareBigDiag f ℱ V) (compareIndexMap f V) ≫
    (HasLimit.isoOfNatIso (compareDiagIso f ℱ V)).hom

/-- Restriction of a small-étale compatible family to the atlas cover `U₀`. -/
def compareCoverSection (V : smallEtaleSite G) :
    limit (compareSmallDiag f ℱ V) ⟶
      ℱ.obj.obj (op ((smallEtaleToGroupoids F).obj (coverSite f V))) :=
  (HasLimit.isoOfNatIso (compareDiagIso f ℱ V)).inv ≫
    limit.π (compareIndexMap f V ⋙ compareBigDiag f ℱ V) (coverIndex f V)

/-- The family of sections of `ℱ` on `T ×_{F ×_G V} U₀` obtained by restricting the atlas
cover section. -/
def compareFibreSection (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiag f ℱ V) ⟶ ℱ.obj.obj (op (compareFibreObj f j)) :=
  compareCoverSection f ℱ V ≫ ℱ.obj.map (compareFibreToCover f j).op

/-- Compatibility of the one-arrow covering family on `T ×_{F ×_G V} U₀`. -/
theorem compareFibreSection_compatible (V : smallEtaleSite G)
    (j : compareBigIndex f V) :
    ∀ ⦃W : F.toGroupoids.total⦄ ⦃i k : Unit⦄
      (a : W ⟶ compareFibreObj f j) (b : W ⟶ compareFibreObj f j),
      a ≫ compareFibreToBig f j = b ≫ compareFibreToBig f j →
        compareFibreSection f ℱ V j ≫ ℱ.obj.map a.op =
          compareFibreSection f ℱ V j ≫ ℱ.obj.map b.op :=
  sorry

/-- Component of the reverse comparison cone at a CFG comma object. -/
def compareInvπ (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiag f ℱ V) ⟶ (compareBigDiag f ℱ V).obj j :=
  ℱ.property.amalgamateOfArrows
    (fun _ : Unit => compareFibreToBig f j)
    (compareFibre_cover_mem f j)
    (fun _ => compareFibreSection f ℱ V j)
    (compareFibreSection_compatible f ℱ V j)

/-- Extension of a small-étale compatible family to a CFG compatible family, by
amalgamating along the étale cover `T ×_{F ×_G V} U₀ ⟶ T`. -/
def compareLimitInv (V : smallEtaleSite G) :
    limit (compareSmallDiag f ℱ V) ⟶ limit (compareBigDiag f ℱ V) :=
  limit.lift (compareBigDiag f ℱ V)
    { pt := limit (compareSmallDiag f ℱ V)
      π :=
        { app := compareInvπ f ℱ V
          naturality := sorry } }

/-- Canonical identification of the two Kan-extension limits at `V`. -/
def compareLimitIso (V : smallEtaleSite G) :
    limit (compareBigDiag f ℱ V) ≅ limit (compareSmallDiag f ℱ V) where
  hom := compareLimitHom f ℱ V
  inv := compareLimitInv f ℱ V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The spaces-étale extension of `ℱ |_{F_étale}` used by `f_small,*`. -/
abbrev compareSmallExtended :
    Sheaf (spacesEtaleTopology F) (Type (u + 1)) :=
  ((AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces F).sheafPushforwardCocontinuous (Type (u + 1))
      (smallEtaleTopology F) (spacesEtaleTopology F)).obj
    ((restrictEtale F).obj ℱ)

/-- Sectionwise identification of `(f_* ℱ)(u_G(V))` with
`f_small,* (ℱ |_{F_étale})(V)`. -/
def compareBigSmall_app (V : smallEtaleSite G) :
    ((restrictEtale G).obj ((etalePushforward f).obj ℱ)).obj.obj (op V) ≅
      ((sheafPushforwardType f).obj ((restrictEtale F).obj ℱ)).obj.obj (op V) :=
  (sheafPushforwardContinuousObjObjIso (smallEtaleToGroupoids G) (Type (u + 1))
      ((etalePushforward f).obj ℱ) V) ≪≫
    (pointwiseRightKanExtensionIsPointwiseRightKanExtension
      (toFunctor (toGroupoids.map f)).op ℱ.obj
      (op ((smallEtaleToGroupoids G).obj V))).isoLimit ≪≫
      compareLimitIso f ℱ V ≪≫
        ((AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces F).op.ranObjObjIsoLimit
            ((restrictEtale F).obj ℱ).obj
            (op ((etaleBaseChange f).obj V))).symm ≪≫
          (sheafPushforwardContinuousObjObjIso (etaleBaseChange f) (Type (u + 1))
              (compareSmallExtended ℱ) V).symm

/-- Underlying presheaf identification of the two composites. -/
def compareBigSmallPresheaf :
    ((restrictEtale G).obj ((etalePushforward f).obj ℱ)).obj ≅
      ((sheafPushforwardType f).obj ((restrictEtale F).obj ℱ)).obj :=
  NatIso.ofComponents (fun V => compareBigSmall_app f ℱ V.unop) sorry

/-- The canonical identification
`(f_* ℱ)|_{G_étale} = f_small,* (ℱ |_{F_étale})` of sheaves on `G_étale`. -/
def compareBigSmall :
    (restrictEtale G).obj ((etalePushforward f).obj ℱ) ≅
      (sheafPushforwardType f).obj ((restrictEtale F).obj ℱ) where
  hom := CategoryTheory.ObjectProperty.homMk (compareBigSmallPresheaf f ℱ).hom
  inv := CategoryTheory.ObjectProperty.homMk (compareBigSmallPresheaf f ℱ).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `compareBigSmall` is the sectionwise identification `compareBigSmall_app`. -/
theorem compareBigSmall_app_eq (V : smallEtaleSite G) :
    ((sheafToPresheaf (smallEtaleTopology G) (Type (u + 1))).mapIso
          (compareBigSmall f ℱ)).app (op V) =
      compareBigSmall_app f ℱ V :=
  sorry

/-- The identification is natural in the étale sheaf `ℱ`. -/
theorem compareBigSmall_natural
    {ℱ 𝒢 : Sheaf F.toGroupoids.etaleTopology (Type (u + 1))} (τ : ℱ ⟶ 𝒢) :
    (restrictEtale G).map ((etalePushforward f).map τ) ≫ (compareBigSmall f 𝒢).hom =
      (compareBigSmall f ℱ).hom ≫
        (sheafPushforwardType f).map ((restrictEtale F).map τ) :=
  sorry

end CompareTypeSucc

/-- The total functor of `toGroupoids.map f` is continuous for associated étale topologies. -/
instance toGroupoids_map_isContinuous_etale {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.IsContinuous
      F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor (toGroupoids.map f))
    (StandardTopology.etale.overTopology S)

/-- The total functor of `toGroupoids.map f` is cocontinuous for associated étale topologies. -/
instance toGroupoids_map_isCocontinuous_etale {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.IsCocontinuous
      F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor (toGroupoids.map f))
    (StandardTopology.etale.overTopology S)

/-- `smallEtaleToGroupoids` agrees with the identity-equivalence specialization of `u`. -/
theorem smallEtaleToGroupoids_eq_smallEtaleFunctor_id (F : AlgebraicSpace S) :
    smallEtaleToGroupoids F = GroupoidsOver.smallEtaleFunctor_id F :=
  sorry

/-- Type-valued restriction uses the same functor `u` as the base of `π_F`. -/
theorem restrictEtale_eq_pi_type (F : AlgebraicSpace S) :
    smallEtaleToGroupoids F =
      (GroupoidsOver.pi F F.toGroupoids
          (Bicategory.Equivalence.id F.toGroupoids)).base :=
  sorry

/-- The total functor of `toGroupoids.map f` is continuous for associated étale topologies. -/
instance toGroupoids_map_toFunctor_isContinuous_etale {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toFunctor (toGroupoids.map f)).IsContinuous
      F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology :=
  sorry

/-- The cartesian total functor of `toGroupoids.map f` agrees with `toFunctor`. -/
theorem toGroupoids_map_cartesian_eq {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor =
      toFunctor (toGroupoids.map f) :=
  congrArg (fun F => F.toFunctor)
    (toCartesianBasedFunctor.toBasedFunctor (toGroupoids.map f))

/-- The composite `toFunctor (toGroupoids.map f) ⋙ G.toGroupoids.p` is continuous
from `F_étale` to the big étale site of `S`. -/
instance toGroupoids_map_comp_p_isContinuous {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (toFunctor (toGroupoids.map f) ⋙ G.toGroupoids.p).IsContinuous
      F.toGroupoids.etaleTopology (StandardTopology.etale.overTopology S) :=
  sorry

/-- Inverse-image form of the structure-sheaf map of `toGroupoids.map f`. -/
def toGroupoidsEtaleStructureSheafInv {F G : AlgebraicSpace S} (f : F ⟶ G) :
    ((toFunctor (toGroupoids.map f)).sheafPushforwardContinuous RingCat.{u}
        F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology).obj
      (GroupoidsOver.etaleRingedSite G.toGroupoids).structureSheaf ⟶
      (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf :=
  (sheafPushforwardContinuousIso (eqToIso (comm (toGroupoids.map f)).symm) RingCat.{u}
      F.toGroupoids.etaleTopology (StandardTopology.etale.overTopology S)).inv.app
    (StandardTopology.Big.structureSheaf StandardTopology.etale S)

/-- The actual per-sheaf direct-image structure map, with the size certificate
derived from the supplied identity presentations of the source and target. -/
def toGroupoidsEtaleStructureSheafMap {F G : AlgebraicSpace S} (f : F ⟶ G) :
    letI := GroupoidsOver.hasSmallCFGTypeSections_ofRepresented (toGroupoids.map f)
      (Bicategory.Equivalence.id F.toGroupoids) (Bicategory.Equivalence.id G.toGroupoids)
    (GroupoidsOver.etaleRingedSite G.toGroupoids).structureSheaf ⟶
      ((toFunctor (toGroupoids.map f)).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u}
        F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology).obj
          (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf :=
  letI := GroupoidsOver.hasSmallCFGTypeSections_ofRepresented (toGroupoids.map f)
    (Bicategory.Equivalence.id F.toGroupoids) (Bicategory.Equivalence.id G.toGroupoids)
  GroupoidsOver.etaleModuleStructureSheafMap (toGroupoids.map f)

/-- The actual direct structure map is compatible with internal ring operations. -/
theorem toGroupoidsEtaleStructureSheafMap_isRingCompatible {F G : AlgebraicSpace S}
    (f : F ⟶ G) :
    letI := GroupoidsOver.hasSmallCFGTypeSections_ofRepresented (toGroupoids.map f)
      (Bicategory.Equivalence.id F.toGroupoids) (Bicategory.Equivalence.id G.toGroupoids)
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (GroupoidsOver.etaleRingedSite F.toGroupoids)
      (GroupoidsOver.etaleRingedSite G.toGroupoids) inferInstance inferInstance
      ((toFunctor (toGroupoids.map f)).morphismOfTopoiOfSmallSheafSections.{u + 1, u, u + 1, u, u}
        F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology)
      ((toFunctor (toGroupoids.map f)).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u}
        F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology)
      ((toFunctor (toGroupoids.map f)).sheafPushforwardRingOfSmallSectionsForgetIso.{u + 1, u, u + 1, u, u}
        F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology)
      (toGroupoidsEtaleStructureSheafMap f) :=
  letI := GroupoidsOver.hasSmallCFGTypeSections_ofRepresented (toGroupoids.map f)
    (Bicategory.Equivalence.id F.toGroupoids) (Bicategory.Equivalence.id G.toGroupoids)
  GroupoidsOver.etaleModuleStructureSheafMap_isRingCompatible (toGroupoids.map f)

/-- The morphism of ringed topoi is the canonical actual per-sheaf direct image. -/
def toGroupoidsEtaleRingedToposHom {F G : AlgebraicSpace S} (f : F ⟶ G) :
    RingedSite.ToposHom
      (GroupoidsOver.etaleRingedSite F.toGroupoids)
      (GroupoidsOver.etaleRingedSite G.toGroupoids) :=
  letI := GroupoidsOver.hasSmallCFGTypeSections_ofRepresented (toGroupoids.map f)
    (Bicategory.Equivalence.id F.toGroupoids) (Bicategory.Equivalence.id G.toGroupoids)
  GroupoidsOver.etaleRingedToposHom (toGroupoids.map f)

/-- Direct image `f_*` of étale `𝒪`-modules along `toGroupoids.map f`. -/
def etaleModulePushforward {F G : AlgebraicSpace S} (f : F ⟶ G) :
    SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf ⥤
      SheafOfModules.{u} (GroupoidsOver.etaleRingedSite G.toGroupoids).structureSheaf :=
  (toGroupoidsEtaleRingedToposHom f).modulePushforward

/-- `etaleModulePushforward` is the module direct image of `toGroupoidsEtaleRingedToposHom`. -/
theorem etaleModulePushforward_eq {F G : AlgebraicSpace S} (f : F ⟶ G) :
    etaleModulePushforward f = (toGroupoidsEtaleRingedToposHom f).modulePushforward :=
  rfl

/-- Restriction of an étale `𝒪`-module on `S_F` to `F_étale`, as module pushforward
along `π_F` for the identity equivalence of `F.toGroupoids`. -/
def restrictEtaleModules (F : AlgebraicSpace S) :
    SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf ⥤
      SheafOfModules.{u} (structureSheaf F) :=
  (GroupoidsOver.pi F F.toGroupoids (Bicategory.Equivalence.id F.toGroupoids)).modulePushforward.{u}

/-- `restrictEtaleModules` is module pushforward along `π_F`. -/
theorem restrictEtaleModules_eq (F : AlgebraicSpace S) :
    restrictEtaleModules F =
      (GroupoidsOver.pi F F.toGroupoids
          (Bicategory.Equivalence.id F.toGroupoids)).modulePushforward.{u} :=
  rfl

/-- Underlying type-valued sheaf of an étale `𝒪`-module on `S_F`. -/
def moduleUnderlyingType {F : AlgebraicSpace S}
    (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf) :
    Sheaf F.toGroupoids.etaleTopology (Type u) :=
  (ToInternal.underlying (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf).obj ℳ

/-- `moduleUnderlyingType` is the forgetful image of an étale `𝒪`-module. -/
theorem moduleUnderlyingType_eq {F : AlgebraicSpace S}
    (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf) :
    moduleUnderlyingType ℳ =
      (ToInternal.underlying
          (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf).obj ℳ :=
  rfl

section CompareModules

variable {F G : AlgebraicSpace S} (f : F ⟶ G)
variable (ℳ : SheafOfModules.{u} (GroupoidsOver.etaleRingedSite F.toGroupoids).structureSheaf)

/-- Evaluation of the restricted CFG module pushforward at `V` recovers sections at `u(V)`. -/
def compareBigSmall_modules_leftEval (V : smallEtaleSite G) :
    ((ToInternal.underlying (structureSheaf G)).obj
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ))).obj.obj (op V) ≅
      ((ToInternal.underlying
          (GroupoidsOver.etaleRingedSite G.toGroupoids).structureSheaf).obj
        ((etaleModulePushforward f).obj ℳ)).obj.obj
          (op ((smallEtaleToGroupoids G).obj V)) :=
  Iso.refl _

/-- The Type-`u` comma diagram computing `f_*` of the underlying sheaf at `u_G(V)`. -/
abbrev compareBigDiagType (V : smallEtaleSite G) :
    compareBigIndex f V ⥤ Type u :=
  StructuredArrow.proj (op ((smallEtaleToGroupoids G).obj V))
      (toCartesianBasedFunctor (toGroupoids.map f)).toFunctor.op ⋙
    (moduleUnderlyingType ℳ).obj

/-- The Type-`u` comma diagram computing `f_small,*` of the restricted underlying sheaf. -/
abbrev compareSmallDiagType (V : smallEtaleSite G) :
    compareSmallIndex f V ⥤ Type u :=
  StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces F).op ⋙
    ((ToInternal.underlying (structureSheaf F)).obj
      ((restrictEtaleModules F).obj ℳ)).obj

/-- Type-valued limits exist for the Type-`u` CFG Kan diagram. -/
instance compareBigDiagType_hasLimit (V : smallEtaleSite G) :
    HasLimit (compareBigDiagType f ℳ V) :=
  HasLimit.mk
    ⟨GroupoidsOver.RepresentedDirectImage.cone (toGroupoids.map f)
      (Bicategory.Equivalence.id F.toGroupoids) (Bicategory.Equivalence.id G.toGroupoids)
      (moduleUnderlyingType ℳ) ((smallEtaleToGroupoids G).obj V),
     GroupoidsOver.RepresentedDirectImage.coneIsLimit (toGroupoids.map f)
      (Bicategory.Equivalence.id F.toGroupoids) (Bicategory.Equivalence.id G.toGroupoids)
      (moduleUnderlyingType ℳ) ((smallEtaleToGroupoids G).obj V)⟩

/-- Type-valued limits exist for the Type-`u` small-étale Kan diagram. -/
instance compareSmallDiagType_hasLimit (V : smallEtaleSite G) :
    HasLimit (compareSmallDiagType f ℳ V) :=
  EtaleTopos.allChartHasLimit F
    ((ToInternal.underlying (structureSheaf F)).obj ((restrictEtaleModules F).obj ℳ))
    ((etaleBaseChange f).obj V)

/-- The Type-`u` Kan diagrams are identified after restriction along `compareIndexMap`. -/
def compareDiagIsoType (V : smallEtaleSite G) :
    compareIndexMap f V ⋙ compareBigDiagType f ℳ V ≅ compareSmallDiagType f ℳ V :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Type-valued limits exist after restriction along `compareIndexMap`. -/
instance compareIndexBigDiagType_hasLimit (V : smallEtaleSite G) :
    HasLimit (compareIndexMap f V ⋙ compareBigDiagType f ℳ V) :=
  hasLimit_of_iso (compareDiagIsoType f ℳ V).symm

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category, in universe `u`. -/
def compareLimitHomType (V : smallEtaleSite G) :
    limit (compareBigDiagType f ℳ V) ⟶ limit (compareSmallDiagType f ℳ V) :=
  limit.pre (compareBigDiagType f ℳ V) (compareIndexMap f V) ≫
    (HasLimit.isoOfNatIso (compareDiagIsoType f ℳ V)).hom

/-- Restriction of a small-étale compatible family to the atlas cover `U₀`, in universe `u`. -/
def compareCoverSectionType (V : smallEtaleSite G) :
    limit (compareSmallDiagType f ℳ V) ⟶
      (moduleUnderlyingType ℳ).obj.obj
        (op ((smallEtaleToGroupoids F).obj (coverSite f V))) :=
  (HasLimit.isoOfNatIso (compareDiagIsoType f ℳ V)).inv ≫
    limit.π (compareIndexMap f V ⋙ compareBigDiagType f ℳ V) (coverIndex f V)

/-- The family of sections of the underlying sheaf on `T ×_{F ×_G V} U₀`. -/
def compareFibreSectionType (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiagType f ℳ V) ⟶
      (moduleUnderlyingType ℳ).obj.obj (op (compareFibreObj f j)) :=
  compareCoverSectionType f ℳ V ≫
    (moduleUnderlyingType ℳ).obj.map (compareFibreToCover f j).op

/-- Compatibility of the one-arrow covering family on `T ×_{F ×_G V} U₀`, in universe `u`. -/
theorem compareFibreSectionType_compatible (V : smallEtaleSite G)
    (j : compareBigIndex f V) :
    ∀ ⦃W : F.toGroupoids.total⦄ ⦃i k : Unit⦄
      (a : W ⟶ compareFibreObj f j) (b : W ⟶ compareFibreObj f j),
      a ≫ compareFibreToBig f j = b ≫ compareFibreToBig f j →
        compareFibreSectionType f ℳ V j ≫ (moduleUnderlyingType ℳ).obj.map a.op =
          compareFibreSectionType f ℳ V j ≫ (moduleUnderlyingType ℳ).obj.map b.op :=
  sorry

/-- Component of the reverse Type-`u` comparison cone at a CFG comma object. -/
def compareInvπType (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiagType f ℳ V) ⟶ (compareBigDiagType f ℳ V).obj j :=
  (moduleUnderlyingType ℳ).property.amalgamateOfArrows
    (fun _ : Unit => compareFibreToBig f j)
    (compareFibre_cover_mem f j)
    (fun _ => compareFibreSectionType f ℳ V j)
    (compareFibreSectionType_compatible f ℳ V j)

/-- Extension of a small-étale compatible family to a CFG compatible family, in universe `u`. -/
def compareLimitInvType (V : smallEtaleSite G) :
    limit (compareSmallDiagType f ℳ V) ⟶ limit (compareBigDiagType f ℳ V) :=
  limit.lift (compareBigDiagType f ℳ V)
    { pt := limit (compareSmallDiagType f ℳ V)
      π :=
        { app := compareInvπType f ℳ V
          naturality := sorry } }

/-- Canonical identification of the two Type-`u` Kan-extension limits at `V`. -/
def compareLimitIsoType (V : smallEtaleSite G) :
    limit (compareBigDiagType f ℳ V) ≅ limit (compareSmallDiagType f ℳ V) where
  hom := compareLimitHomType f ℳ V
  inv := compareLimitInvType f ℳ V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Evaluation of the small étale module pushforward at `V` recovers the Type-`u`
Kan limit. -/
def compareBigSmall_modules_rightEval (V : smallEtaleSite G) :
    limit (compareSmallDiagType f ℳ V) ≅
      ((ToInternal.underlying (structureSheaf G)).obj
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ))).obj.obj (op V) :=
  (limit.isoLimitCone
    ⟨EtaleTopos.allChartCone F
      ((ToInternal.underlying (structureSheaf F)).obj ((restrictEtaleModules F).obj ℳ))
      ((etaleBaseChange f).obj V),
     EtaleTopos.allChartIsLimit F
      ((ToInternal.underlying (structureSheaf F)).obj ((restrictEtaleModules F).obj ℳ))
      ((etaleBaseChange f).obj V)⟩) ≪≫
    ((sheafToPresheaf (smallEtaleTopology G) (Type u)).mapIso
        ((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).app
          ((restrictEtaleModules F).obj ℳ))).symm.app (op V)

/-- Sectionwise type-valued comparison underlying the `𝒪_G`-module identification. -/
def compareBigSmall_modules_app (V : smallEtaleSite G) :
    ((ToInternal.underlying (structureSheaf G)).obj
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ))).obj.obj (op V) ≅
      ((ToInternal.underlying (structureSheaf G)).obj
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ))).obj.obj (op V) :=
  letI := GroupoidsOver.hasSmallCFGTypeSections_ofRepresented (toGroupoids.map f)
    (Bicategory.Equivalence.id F.toGroupoids) (Bicategory.Equivalence.id G.toGroupoids)
  compareBigSmall_modules_leftEval f ℳ V ≪≫
    ((sheafToPresheaf G.toGroupoids.etaleTopology (Type u)).mapIso
        ((RingedSite.ToposHom.ModulePushforward.forgetIso
            (toGroupoidsEtaleRingedToposHom f)).app ℳ)).app
      (op ((smallEtaleToGroupoids G).obj V)) ≪≫
      (pointwiseRightKanExtensionIsPointwiseRightKanExtension
        (toFunctor (toGroupoids.map f)).op (moduleUnderlyingType ℳ).obj
        (op ((smallEtaleToGroupoids G).obj V))).isoLimit ≪≫
        (compareLimitIsoType f ℳ V) ≪≫
          compareBigSmall_modules_rightEval f ℳ V

/-- Underlying type-valued morphism of the `𝒪_G`-module identification. -/
def compareBigSmall_modules_underlying :
    (ToInternal.underlying (structureSheaf G)).obj
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ)) ⟶
      (ToInternal.underlying (structureSheaf G)).obj
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ)) :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun V => (compareBigSmall_modules_app f ℳ V.unop).hom
      naturality := sorry }

/-- Inverse underlying type-valued morphism of the `𝒪_G`-module identification. -/
def compareBigSmall_modules_underlyingInv :
    (ToInternal.underlying (structureSheaf G)).obj
        ((Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ)) ⟶
      (ToInternal.underlying (structureSheaf G)).obj
        ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ)) :=
  CategoryTheory.ObjectProperty.homMk
    { app := fun V => (compareBigSmall_modules_app f ℳ V.unop).inv
      naturality := sorry }

/-- The identification `(f_* ℳ)|_{G_étale} ≅ f_small,* (ℳ |_{F_étale})` as an
isomorphism of `𝒪_G`-modules on `G_étale`. -/
def compareBigSmall_modules :
    (restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ) ≅
      (Modules.pushforward f).obj ((restrictEtaleModules F).obj ℳ) where
  hom := homOfUnderlying (structureSheaf G)
    (compareBigSmall_modules_underlying f ℳ) sorry sorry
  inv := homOfUnderlying (structureSheaf G)
    (compareBigSmall_modules_underlyingInv f ℳ) sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying type-valued sheaf map of `compareBigSmall_modules` is
`compareBigSmall_modules_underlying`. -/
theorem compareBigSmall_modules_forget :
    (ToInternal.underlying (structureSheaf G)).map (compareBigSmall_modules f ℳ).hom =
      compareBigSmall_modules_underlying f ℳ :=
  sorry

/-- The forward map of `compareBigSmall_modules` is `𝒪_G`-linear. -/
theorem compareBigSmall_modules_isLinear (V : (smallEtaleSite G)ᵒᵖ)
    (r : (structureSheaf G).obj.obj V)
    (x : ((restrictEtaleModules G).obj ((etaleModulePushforward f).obj ℳ)).val.obj V) :
    (compareBigSmall_modules f ℳ).hom.val.app V (r • x) =
      r • (compareBigSmall_modules f ℳ).hom.val.app V x :=
  sorry

end CompareModules

end AlgebraicGeometry.AlgebraicSpace
