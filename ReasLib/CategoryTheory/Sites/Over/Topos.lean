module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Limits.Over.FiniteConnected
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits

/-!
# Sheaf functors on slice sites

This leaf packages the topology-independent part of the usual construction
attached to a morphism `f : T ⟶ S`: postcomposition on `Over T`, its pullback
right adjoint, and the induced sheaf and topos functors.  A topology on the
ambient category is the only site-specific input.  Concrete big-site modules
should provide the continuity and cocontinuity instances and use this API as
their neutral owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe uC vC w

namespace CategoryTheory
namespace Over
namespace Site

variable {C : Type uC} [Category.{vC} C]
variable {S T : C}

/-- Postcomposition on slice categories. -/
abbrev mapFunctor (f : T ⟶ S) : Over T ⥤ Over S :=
  Over.map f

/-- Pullback on slice categories. -/
abbrev pullbackFunctor (f : T ⟶ S) [HasPullbacksAlong f] : Over S ⥤ Over T :=
  Over.pullback f

/-- The canonical postcomposition-pullback adjunction on slice categories. -/
abbrev mapPullbackAdjunction (f : T ⟶ S) [HasPullbacksAlong f] :
    mapFunctor f ⊣ pullbackFunctor f :=
  Over.mapPullbackAdj f

/-- The inverse-image functor on sheaves induced by postcomposition. -/
abbrev inverseImage (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)] :
    Sheaf (J.over S) (Type w) ⥤ Sheaf (J.over T) (Type w) :=
  (mapFunctor f).sheafPushforwardContinuous (Type w) (J.over T) (J.over S)

namespace InverseImage

/-- The inverse image is computed by evaluating on the postcomposed slice object. -/
@[stacks 0EU6]
theorem obj_eq (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    (𝒢 : Sheaf (J.over S) (Type w)) (U : Over T) :
    ((inverseImage J f).obj 𝒢).obj.obj (op U) =
      𝒢.obj.obj (op ((mapFunctor f).obj U)) := sorry

end InverseImage

/-- The objectwise inverse-image computation as a canonical isomorphism. -/
noncomputable def InverseImage.objIso (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    (𝒢 : Sheaf (J.over S) (Type w)) (U : Over T) :
    ((inverseImage J f).obj 𝒢).obj.obj (op U) ≅
      𝒢.obj.obj (op ((mapFunctor f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (mapFunctor f) (Type w) 𝒢 U

/-- The forward inverse-image comparison is natural in the slice object. -/
theorem InverseImage.objIso.naturality_obj (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    (𝒢 : Sheaf (J.over S) (Type w)) {U V : Over T} (φ : U ⟶ V) :
    (InverseImage.objIso J f 𝒢 V).hom ≫
        𝒢.obj.map ((mapFunctor f).map φ).op =
      ((inverseImage J f).obj 𝒢).obj.map φ.op ≫
        (InverseImage.objIso J f 𝒢 U).hom := sorry

/-- The inverse inverse-image comparison is natural in the slice object. -/
theorem InverseImage.objIso.inv_naturality_obj
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    (𝒢 : Sheaf (J.over S) (Type w)) {U V : Over T} (φ : U ⟶ V) :
    𝒢.obj.map ((mapFunctor f).map φ).op ≫
        (InverseImage.objIso J f 𝒢 U).inv =
      (InverseImage.objIso J f 𝒢 V).inv ≫
        ((inverseImage J f).obj 𝒢).obj.map φ.op := sorry

/-- The forward inverse-image comparison is natural in the sheaf argument. -/
theorem InverseImage.objIso.naturality_sheaf
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    {𝒢 ℋ : Sheaf (J.over S) (Type w)} (η : 𝒢 ⟶ ℋ) (U : Over T) :
    ((inverseImage J f).map η).hom.app (op U) ≫
        (InverseImage.objIso J f ℋ U).hom =
      (InverseImage.objIso J f 𝒢 U).hom ≫
        η.hom.app (op ((mapFunctor f).obj U)) := sorry

/-- The inverse inverse-image comparison is natural in the sheaf argument. -/
theorem InverseImage.objIso.inv_naturality_sheaf
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    {𝒢 ℋ : Sheaf (J.over S) (Type w)} (η : 𝒢 ⟶ ℋ) (U : Over T) :
    η.hom.app (op ((mapFunctor f).obj U)) ≫
        (InverseImage.objIso J f ℋ U).inv =
      (InverseImage.objIso J f 𝒢 U).inv ≫
        ((inverseImage J f).map η).hom.app (op U) := sorry

/-- The direct-image functor on sheaves induced by postcomposition. -/
abbrev directImage (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P] :
    Sheaf (J.over T) (Type w) ⥤ Sheaf (J.over S) (Type w) :=
  (mapFunctor f).sheafPushforwardCocontinuous (Type w) (J.over T) (J.over S)

/-- The direct image is computed by evaluating on the pullback slice object. -/
theorem DirectImage.obj_eq (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [HasPullbacksAlong f] (ℱ : Sheaf (J.over T) (Type w)) (U : Over S) :
    ((directImage J f).obj ℱ).obj.obj (op U) =
      ℱ.obj.obj (op ((pullbackFunctor f).obj U)) := sorry

/-- The objectwise direct-image computation as a canonical isomorphism. -/
noncomputable def DirectImage.objIso (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [HasPullbacksAlong f]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    (ℱ : Sheaf (J.over T) (Type w)) (U : Over S) :
    ((directImage J f).obj ℱ).obj.obj (op U) ≅
      ℱ.obj.obj (op ((pullbackFunctor f).obj U)) :=
  Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    (mapFunctor f) (pullbackFunctor f) (Type w)
    (mapPullbackAdjunction f) ℱ U

/-- The forward direct-image comparison is natural in the slice object. -/
theorem DirectImage.objIso.naturality_obj (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [HasPullbacksAlong f]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    (ℱ : Sheaf (J.over T) (Type w))
    {U V : Over S} (φ : U ⟶ V) :
    (DirectImage.objIso J f ℱ V).hom ≫
        ℱ.obj.map ((pullbackFunctor f).map φ).op =
      ((directImage J f).obj ℱ).obj.map φ.op ≫
        (DirectImage.objIso J f ℱ U).hom := sorry

/-- The inverse direct-image comparison is natural in the slice object. -/
theorem DirectImage.objIso.inv_naturality_obj
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [HasPullbacksAlong f]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    (ℱ : Sheaf (J.over T) (Type w)) {U V : Over S} (φ : U ⟶ V) :
    ℱ.obj.map ((pullbackFunctor f).map φ).op ≫
        (DirectImage.objIso J f ℱ U).inv =
      (DirectImage.objIso J f ℱ V).inv ≫
        ((directImage J f).obj ℱ).obj.map φ.op := sorry

/-- The forward direct-image comparison is natural in the sheaf argument. -/
theorem DirectImage.objIso.naturality_sheaf
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [HasPullbacksAlong f]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    {ℱ 𝒢 : Sheaf (J.over T) (Type w)} (η : ℱ ⟶ 𝒢) (U : Over S) :
    ((directImage J f).map η).hom.app (op U) ≫
        (DirectImage.objIso J f 𝒢 U).hom =
      (DirectImage.objIso J f ℱ U).hom ≫
        η.hom.app (op ((pullbackFunctor f).obj U)) := sorry

/-- The inverse direct-image comparison is natural in the sheaf argument. -/
theorem DirectImage.objIso.inv_naturality_sheaf
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [HasPullbacksAlong f]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    {ℱ 𝒢 : Sheaf (J.over T) (Type w)} (η : ℱ ⟶ 𝒢) (U : Over S) :
    η.hom.app (op ((pullbackFunctor f).obj U)) ≫
        (DirectImage.objIso J f 𝒢 U).inv =
      (DirectImage.objIso J f ℱ U).inv ≫
        ((directImage J f).map η).hom.app (op U) := sorry

/-- The bundled morphism of topoi presented cocontinuously by postcomposition. -/
@[stacks 04IY "underlying relocalization"]
noncomputable def morphismOfTopoi (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn.{max uC vC, max uC vC, vC, vC, w} (J.over S) (J.over T) where
  inverseImageFunctor := LeftExactFunctor.of (inverseImage J f)
  pushforward := directImage J f
  adjunction := (mapFunctor f).sheafAdjunctionCocontinuous (Type w) (J.over T) (J.over S)

/-- The inverse-image projection of the bundled slice morphism. -/
@[simp]
theorem Morphism.inverseImage (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P] :
    (morphismOfTopoi J f)⁻¹ = inverseImage J f := sorry

/-- The inverse-image computation for the bundled slice morphism. -/
noncomputable def Morphism.inverseImageObjIso
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    (𝒢 : Sheaf (J.over S) (Type w)) (U : Over T) :
    (((morphismOfTopoi J f)⁻¹).obj 𝒢).obj.obj (op U) ≅
      𝒢.obj.obj (op ((mapFunctor f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj 𝒢).obj.obj (op U))
    (Morphism.inverseImage J f)) ≪≫
      InverseImage.objIso J f 𝒢 U

/-- The forward bundled inverse-image comparison is natural in the slice object. -/
theorem Morphism.inverseImageObjIso.naturality_obj
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    (𝒢 : Sheaf (J.over S) (Type w)) {U V : Over T} (φ : U ⟶ V) :
    (Morphism.inverseImageObjIso J f 𝒢 V).hom ≫
        𝒢.obj.map ((mapFunctor f).map φ).op =
      (((morphismOfTopoi J f)⁻¹).obj 𝒢).obj.map φ.op ≫
        (Morphism.inverseImageObjIso J f 𝒢 U).hom := sorry

/-- The inverse bundled inverse-image comparison is natural in the slice object. -/
theorem Morphism.inverseImageObjIso.inv_naturality_obj
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    (𝒢 : Sheaf (J.over S) (Type w)) {U V : Over T} (φ : U ⟶ V) :
    𝒢.obj.map ((mapFunctor f).map φ).op ≫
        (Morphism.inverseImageObjIso J f 𝒢 U).inv =
      (Morphism.inverseImageObjIso J f 𝒢 V).inv ≫
        (((morphismOfTopoi J f)⁻¹).obj 𝒢).obj.map φ.op := sorry

/-- The forward bundled inverse-image comparison is natural in the sheaf argument. -/
theorem Morphism.inverseImageObjIso.naturality_sheaf
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    {𝒢 ℋ : Sheaf (J.over S) (Type w)} (η : 𝒢 ⟶ ℋ) (U : Over T) :
    (((morphismOfTopoi J f)⁻¹).map η).hom.app (op U) ≫
        (Morphism.inverseImageObjIso J f ℋ U).hom =
      (Morphism.inverseImageObjIso J f 𝒢 U).hom ≫
        η.hom.app (op ((mapFunctor f).obj U)) := sorry

/-- The inverse bundled inverse-image comparison is natural in the sheaf argument. -/
theorem Morphism.inverseImageObjIso.inv_naturality_sheaf
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    {𝒢 ℋ : Sheaf (J.over S) (Type w)} (η : 𝒢 ⟶ ℋ) (U : Over T) :
    η.hom.app (op ((mapFunctor f).obj U)) ≫
        (Morphism.inverseImageObjIso J f ℋ U).inv =
      (Morphism.inverseImageObjIso J f 𝒢 U).inv ≫
        (((morphismOfTopoi J f)⁻¹).map η).hom.app (op U) := sorry

/-- The direct-image projection of the bundled slice morphism. -/
@[simp]
theorem Morphism.pushforward (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P] :
    (morphismOfTopoi J f).pushforward = directImage J f := sorry

/-- The direct-image comparison with the continuous pullback presentation. -/
noncomputable def DirectImage.pullbackPresentation (J : GrothendieckTopology C)
    (f : T ⟶ S) [HasPullbacksAlong f]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)] :
    directImage J f ≅
      (pullbackFunctor f).sheafPushforwardContinuous (Type w) (J.over S) (J.over T) :=
  (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (mapFunctor f) (pullbackFunctor f) (Type w) (mapPullbackAdjunction f)).symm

/-- The direct-image comparison for the bundled slice morphism. -/
noncomputable def Morphism.pushforwardPresentation
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [HasPullbacksAlong f]
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)] :
    (morphismOfTopoi J f).pushforward ≅
      (pullbackFunctor f).sheafPushforwardContinuous (Type w) (J.over S) (J.over T) :=
  eqToIso (Morphism.pushforward J f) ≪≫ DirectImage.pullbackPresentation J f

/-- The direct-image objectwise computation for the bundled slice morphism. -/
noncomputable def Morphism.pushforwardObjIso
    (J : GrothendieckTopology C) (f : T ⟶ S) [HasPullbacksAlong f]
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    (ℱ : Sheaf (J.over T) (Type w)) (U : Over S) :
    (((morphismOfTopoi J f).pushforward.obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullbackFunctor f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj ℱ).obj.obj (op U))
    (Morphism.pushforward J f)) ≪≫
      DirectImage.objIso J f ℱ U

/-- The forward bundled direct-image comparison is natural in the slice object. -/
theorem Morphism.pushforwardObjIso.naturality_obj
    (J : GrothendieckTopology C) (f : T ⟶ S) [HasPullbacksAlong f]
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    (ℱ : Sheaf (J.over T) (Type w)) {U V : Over S} (φ : U ⟶ V) :
    (Morphism.pushforwardObjIso J f ℱ V).hom ≫
        ℱ.obj.map ((pullbackFunctor f).map φ).op =
      ((morphismOfTopoi J f).pushforward.obj ℱ).obj.map φ.op ≫
        (Morphism.pushforwardObjIso J f ℱ U).hom := sorry

/-- The inverse bundled direct-image comparison is natural in the slice object. -/
theorem Morphism.pushforwardObjIso.inv_naturality_obj
    (J : GrothendieckTopology C) (f : T ⟶ S) [HasPullbacksAlong f]
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    (ℱ : Sheaf (J.over T) (Type w)) {U V : Over S} (φ : U ⟶ V) :
    ℱ.obj.map ((pullbackFunctor f).map φ).op ≫
        (Morphism.pushforwardObjIso J f ℱ U).inv =
      (Morphism.pushforwardObjIso J f ℱ V).inv ≫
        ((morphismOfTopoi J f).pushforward.obj ℱ).obj.map φ.op := sorry

/-- The forward bundled direct-image comparison is natural in the sheaf argument. -/
theorem Morphism.pushforwardObjIso.naturality_sheaf
    (J : GrothendieckTopology C) (f : T ⟶ S) [HasPullbacksAlong f]
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    {ℱ 𝒢 : Sheaf (J.over T) (Type w)} (η : ℱ ⟶ 𝒢) (U : Over S) :
    ((morphismOfTopoi J f).pushforward.map η).hom.app (op U) ≫
        (Morphism.pushforwardObjIso J f 𝒢 U).hom =
      (Morphism.pushforwardObjIso J f ℱ U).hom ≫
        η.hom.app (op ((pullbackFunctor f).obj U)) := sorry

/-- The inverse bundled direct-image comparison is natural in the sheaf argument. -/
theorem Morphism.pushforwardObjIso.inv_naturality_sheaf
    (J : GrothendieckTopology C) (f : T ⟶ S) [HasPullbacksAlong f]
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (pullbackFunctor f) (J.over S) (J.over T)]
    {ℱ 𝒢 : Sheaf (J.over T) (Type w)} (η : ℱ ⟶ 𝒢) (U : Over S) :
    η.hom.app (op ((pullbackFunctor f).obj U)) ≫
        (Morphism.pushforwardObjIso J f 𝒢 U).inv =
      (Morphism.pushforwardObjIso J f ℱ U).inv ≫
        ((morphismOfTopoi J f).pushforward.map η).hom.app (op U) := sorry

/-- The lower-shriek functor on slice sheaves. -/
abbrev lowerShriek (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P] :
    Sheaf (J.over T) (Type w) ⥤ Sheaf (J.over S) (Type w) :=
  (mapFunctor f).sheafPullback (Type w) (J.over T) (J.over S)

/-- The lower-shriek/inverse-image adjunction on slice sheaves. -/
noncomputable def LowerShriek.adjunction (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P] :
    lowerShriek J f ⊣ inverseImage J f :=
  (mapFunctor f).sheafAdjunctionContinuous (Type w) (J.over T) (J.over S)

namespace LowerShriek

/-- The lower-shriek adjunction with the inverse-image projection of the bundled slice morphism. -/
@[stacks 0EU6]
noncomputable def adjunction_viaMorphism (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P] :
    lowerShriek J f ⊣ (morphismOfTopoi J f)⁻¹ :=
  (LowerShriek.adjunction J f).ofNatIsoRight
    (eqToIso (Morphism.inverseImage J f)).symm

end LowerShriek

/-- The lower-shriek functor preserves all finite connected limits. -/
theorem LowerShriek.preservesFiniteConnectedLimits
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [HasFiniteConnectedLimits C] :
    PreservesFiniteConnectedLimits (lowerShriek J f) := sorry

/-- The aggregate finite-connected-limit result projected to pullbacks. -/
theorem LowerShriek.preservesPullbacks
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [HasFiniteConnectedLimits C] :
    PreservesLimitsOfShape WalkingCospan (lowerShriek J f) := sorry

/-- The aggregate finite-connected-limit result projected to equalizers. -/
theorem LowerShriek.preservesEqualizers
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [HasFiniteConnectedLimits C] :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek J f) := sorry

namespace LowerShriek.Pullbacks

/-- Pullback and equalizer existence and preservation give finite-connected-limit preservation
for the lower-shriek functor. -/
theorem ofEqualizers
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [HasPullbacks (Over T)] [HasEqualizers (Over T)]
    [PreservesLimitsOfShape WalkingCospan (mapFunctor f)]
    [PreservesLimitsOfShape WalkingParallelPair (mapFunctor f)] :
    PreservesFiniteConnectedLimits (lowerShriek J f) := sorry

/-- The pullback/equalizer criterion projected to an arbitrary finite connected shape. -/
theorem preservesLimitsOfShape
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [HasPullbacks (Over T)] [HasEqualizers (Over T)]
    [PreservesLimitsOfShape WalkingCospan (mapFunctor f)]
    [PreservesLimitsOfShape WalkingParallelPair (mapFunctor f)]
    (I : Type*) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (lowerShriek J f) := sorry

/-- The pullback/equalizer criterion specialized to preservation of pullbacks. -/
theorem preservesPullbacks
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [HasPullbacks (Over T)] [HasEqualizers (Over T)]
    [PreservesLimitsOfShape WalkingCospan (mapFunctor f)]
    [PreservesLimitsOfShape WalkingParallelPair (mapFunctor f)] :
    PreservesLimitsOfShape WalkingCospan (lowerShriek J f) := sorry

/-- The pullback/equalizer criterion specialized to preservation of equalizers. -/
theorem preservesEqualizers
    (J : GrothendieckTopology C) (f : T ⟶ S)
    [Functor.IsContinuous (mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [HasPullbacks (Over T)] [HasEqualizers (Over T)]
    [PreservesLimitsOfShape WalkingCospan (mapFunctor f)]
    [PreservesLimitsOfShape WalkingParallelPair (mapFunctor f)] :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek J f) := sorry

end LowerShriek.Pullbacks

end Site
end Over
end CategoryTheory
