/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Pullback
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Internal
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_18_10_FMap
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap71.Definition_71_10_3_MeromorphicSection
public import stacks_project.Chap71.Definition_71_10_6_Pullback

/-!
# Pullback of meromorphic sections on algebraic spaces

A morphism of algebraic spaces for which pullbacks of meromorphic functions are defined
induces a canonical map on meromorphic sections of any module sheaf, assembled from
étale-square localization maps, the cone/limit/Ran presentation of small étale pushforward,
and the global-sections identification Γ(f_* G) ≅ Γ(G).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open SheafOfModules.RingedSite
open PresheafOfModules
open Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Abelian-group-valued sheaves in universe `u + 1` on the small étale site compose with the
forgetful functor to types. -/
instance smallEtaleTopology_hasSheafCompose_forget_addCommGrp_succ (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose (forget AddCommGrpCat.{u + 1}) :=
  sorry

/-- Abelian-group-valued sheaves in universe `u + 1` on the spaces étale site compose with the
forgetful functor to types. -/
instance spacesEtaleTopology_hasSheafCompose_forget_addCommGrp_succ (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).HasSheafCompose (forget AddCommGrpCat.{u + 1}) :=
  sorry

/-- Forgetting abelian groups preserves the right Kan extensions along `smallEtaleInclusion`. -/
instance forget_addCommGrpCat_preservesRightKanExtensions_smallEtaleInclusion
    (X : AlgebraicSpace S) :
    (forget AddCommGrpCat.{u + 1}).PreservesRightKanExtensions (smallEtaleInclusion X).op :=
  sorry

/-- Inverse image of type-valued sheaves in universe `u + 1` along a morphism of algebraic spaces
preserves finite limits. -/
instance sheafPushforwardType_leftAdjoint_preservesFiniteLimits {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : PreservesFiniteLimits (sheafPushforwardType f).leftAdjoint :=
  sorry

/-- The type-valued sheaf underlying `𝒦_X(F)`. -/
def meromorphicSectionTypeSheaf (X : AlgebraicSpace S) (F : X.Modules) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  (sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u + 1})).obj
    ((SheafOfModules.toSheaf _).obj (meromorphicSectionSheaf X F))

/-- The underlying functor of `meromorphicSectionTypeSheaf` is the forgetful image of the
abelian sheaf of meromorphic sections. -/
theorem meromorphicSectionTypeSheaf_obj (X : AlgebraicSpace S) (F : X.Modules) :
    (meromorphicSectionTypeSheaf X F).obj =
      (meromorphicSectionSheaf X F).val.presheaf ⋙ forget AddCommGrpCat.{u + 1} :=
  sorry

/-- Direct image of abelian sheaves in universe `u + 1` commutes with forgetting to types. -/
def sheafPushforwardAbelianForgetIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafPushforwardAbelian f ⋙
        sheafCompose (smallEtaleTopology Y) (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u + 1}) ⋙
        sheafPushforwardType f :=
  let u := smallEtaleInclusion X
  let v := etaleBaseChange f
  let F := forget AddCommGrpCat.{u + 1}
  let Ju := smallEtaleTopology X
  let Ku := spacesEtaleTopology X
  let Jv := smallEtaleTopology Y
  (Functor.associator
      (u.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1} Ju Ku)
      (v.sheafPushforwardContinuous AddCommGrpCat.{u + 1} Jv Ku)
      (sheafCompose Jv F)) ≪≫
    Functor.isoWhiskerLeft (u.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1} Ju Ku)
      (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose v F Jv Ku)) ≪≫
    (Functor.associator
        (u.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1} Ju Ku)
        (sheafCompose Ku F)
        (v.sheafPushforwardContinuous (Type (u + 1)) Jv Ku)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPushforwardCocontinuous.compSheafComposeIso u F Ju Ku)
      (v.sheafPushforwardContinuous (Type (u + 1)) Jv Ku) ≪≫
    Functor.associator
      (sheafCompose Ju F)
      (u.sheafPushforwardCocontinuous (Type (u + 1)) Ju Ku)
      (v.sheafPushforwardContinuous (Type (u + 1)) Jv Ku)

/-- `sheafPushforwardAbelianForgetIso` is the coefficient-forgetful comparison of
`sheafPushforwardAbelian`. -/
theorem sheafPushforwardAbelianForgetIso_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafPushforwardAbelianForgetIso f =
      let u := smallEtaleInclusion X
      let v := etaleBaseChange f
      let F := forget AddCommGrpCat.{u + 1}
      let Ju := smallEtaleTopology X
      let Ku := spacesEtaleTopology X
      let Jv := smallEtaleTopology Y
      (Functor.associator
          (u.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1} Ju Ku)
          (v.sheafPushforwardContinuous AddCommGrpCat.{u + 1} Jv Ku)
          (sheafCompose Jv F)) ≪≫
        Functor.isoWhiskerLeft (u.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1} Ju Ku)
          (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose v F Jv Ku)) ≪≫
        (Functor.associator
            (u.sheafPushforwardCocontinuous AddCommGrpCat.{u + 1} Ju Ku)
            (sheafCompose Ku F)
            (v.sheafPushforwardContinuous (Type (u + 1)) Jv Ku)).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.sheafPushforwardCocontinuous.compSheafComposeIso u F Ju Ku)
          (v.sheafPushforwardContinuous (Type (u + 1)) Jv Ku) ≪≫
        Functor.associator
          (sheafCompose Ju F)
          (u.sheafPushforwardCocontinuous (Type (u + 1)) Ju Ku)
          (v.sheafPushforwardContinuous (Type (u + 1)) Jv Ku) :=
  sorry

/-- The morphism of small étale topoi in universe `u + 1` associated to a morphism of algebraic
spaces. -/
def morphismOfTopoiSucc {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) where
  inverseImageFunctor := LeftExactFunctor.of (sheafPushforwardType f).leftAdjoint
  pushforward := sheafPushforwardType f
  adjunction := Adjunction.ofIsRightAdjoint (sheafPushforwardType f)

/-- The direct image of `morphismOfTopoiSucc f` is `sheafPushforwardType f`. -/
theorem morphismOfTopoiSucc_pushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (morphismOfTopoiSucc f).pushforward = sheafPushforwardType f :=
  sorry

/-- Pullback of the underlying type-valued module sections along an étale square. -/
def pullbackModuleSection {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f)
    (F : Y.Modules) :
    ((ToInternal.underlying (structureSheaf Y)).obj F).obj.obj (op sq.right) ⟶
      ((ToInternal.underlying (structureSheaf X)).obj
        ((Modules.pullback f).obj F)).obj.obj (op sq.left) :=
  let F' := (Modules.pullback f).obj F
  let ℱ := (ToInternal.underlying (structureSheaf X)).obj F'
  ((ToInternal.underlying (structureSheaf Y)).map
        ((Modules.pullbackPushforwardAdjunction f).unit.app F) ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).hom.app F').hom.app
      (op sq.right) ≫
    EtaleTopos.extensionEvaluation X ℱ (EtaleTopos.squareArrow f sq)

/-- Applying `pullbackModuleSection` is evaluation of the adjunction unit followed by the
Ran/limit component of `f_*`. -/
theorem pullbackModuleSection_eq {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f)
    (F : Y.Modules) :
    pullbackModuleSection sq F =
      let F' := (Modules.pullback f).obj F
      let ℱ := (ToInternal.underlying (structureSheaf X)).obj F'
      ((ToInternal.underlying (structureSheaf Y)).map
            ((Modules.pullbackPushforwardAdjunction f).unit.app F) ≫
          (RingedSite.ToposHom.ModulePushforward.forgetIso
            (ringedToposHom f)).hom.app F').hom.app (op sq.right) ≫
        EtaleTopos.extensionEvaluation X ℱ (EtaleTopos.squareArrow f sq) :=
  rfl

/-- Pullback of universe-lifted module sections along an étale square. -/
def pullbackLiftedModuleSection {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f)
    (F : Y.Modules) :
    (Modules.liftModule F).val.obj (op sq.right) →
      (Modules.liftModule ((Modules.pullback f).obj F)).val.obj (op sq.left) :=
  fun m ↦ ULift.up (pullbackModuleSection sq F m.down)

/-- Applying `pullbackLiftedModuleSection` is `ULift` of `pullbackModuleSection`. -/
theorem pullbackLiftedModuleSection_eq {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (sq : EtaleSquare f) (F : Y.Modules)
    (m : (Modules.liftModule F).val.obj (op sq.right)) :
    pullbackLiftedModuleSection sq F m =
      ULift.up (pullbackModuleSection sq F m.down) :=
  sorry

/-- Representative-wise pullback of a localized meromorphic section along an étale square. -/
def pullbackMeromorphicSectionRep {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (sq : EtaleSquare f) (F : Y.Modules)
    (p : (Modules.liftModule F).val.obj (op sq.right) ×
      (regularStructureSections Y).obj (op sq.right)) :
    LocalizedModule ((regularStructureSections X).obj (op sq.left))
      ((Modules.liftModule ((Modules.pullback f).obj F)).val.obj (op sq.left)) :=
  LocalizedModule.mk (pullbackLiftedModuleSection sq F p.1)
    ⟨(pullbackStructureSection sq).hom p.2, pullbackStructureSection_mem sq p.2.property⟩

/-- Representative-wise pullback of localized meromorphic sections is independent of the
chosen fraction. -/
theorem pullbackMeromorphicSectionRep_wd {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (sq : EtaleSquare f) (F : Y.Modules)
    (p p' : (Modules.liftModule F).val.obj (op sq.right) ×
      (regularStructureSections Y).obj (op sq.right)) (hp : p ≈ p') :
    pullbackMeromorphicSectionRep sq F p = pullbackMeromorphicSectionRep sq F p' :=
  sorry

/-- Objectwise pullback of localized meromorphic sections along an étale square. -/
def pullbackMeromorphicSectionObj {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (sq : EtaleSquare f) (F : Y.Modules) :
    (meromorphicSectionPresheaf Y F).presheaf.obj (op sq.right) ⟶
      (meromorphicSectionPresheaf X ((Modules.pullback f).obj F)).presheaf.obj
        (op sq.left) :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦
        LocalizedModule.liftOn x (pullbackMeromorphicSectionRep sq F)
          (pullbackMeromorphicSectionRep_wd sq F)
      map_zero' := sorry
      map_add' := sorry }

/-- Applying `pullbackMeromorphicSectionObj` to a fraction recovers the representative-wise
formula. -/
theorem pullbackMeromorphicSectionObj_mk {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (sq : EtaleSquare f) (F : Y.Modules)
    (m : (Modules.liftModule F).val.obj (op sq.right))
    (s : (regularStructureSections Y).obj (op sq.right)) :
    (pullbackMeromorphicSectionObj sq F).hom (LocalizedModule.mk m s) =
      pullbackMeromorphicSectionRep sq F (m, s) :=
  sorry

/-- The sheafification unit of the meromorphic-section presheaf, as an abelian-group map. -/
def meromorphicSectionToSheafApp (X : AlgebraicSpace S) (F : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (meromorphicSectionPresheaf X F).presheaf.obj U ⟶
      ((SheafOfModules.toSheaf _).obj (meromorphicSectionSheaf X F)).obj.obj U :=
  (CategoryTheory.toSheafify (smallEtaleTopology X)
      (meromorphicSectionPresheaf X F).presheaf).app U

/-- `meromorphicSectionToSheafApp` is the sheafification unit of the meromorphic-section
presheaf. -/
theorem meromorphicSectionToSheafApp_eq (X : AlgebraicSpace S) (F : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) :
    meromorphicSectionToSheafApp X F U =
      (CategoryTheory.toSheafify (smallEtaleTopology X)
          (meromorphicSectionPresheaf X F).presheaf).app U :=
  sorry

/-- The cone of étale-square localization maps presenting
`𝒦_Y(F)(V) ⟶ 𝒦_X(f^* F)(X ×_Y V)`. -/
def pullbackMeromorphicSectionCone {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) (V : smallEtaleSite Y) :
    Cone
      (StructuredArrow.proj (op ((etaleBaseChange f).obj V)) (smallEtaleInclusion X).op ⋙
        ((SheafOfModules.toSheaf _).obj
            (meromorphicSectionSheaf X ((Modules.pullback f).obj F))).obj) where
  pt := (meromorphicSectionPresheaf Y F).presheaf.obj (op V)
  π :=
    { app := fun a ↦
        pullbackMeromorphicSectionObj (etaleSquareOfArrow f V a) F ≫
          meromorphicSectionToSheafApp X ((Modules.pullback f).obj F) a.right
      naturality := fun _ _ _ ↦ sorry }

/-- The component at `V` of the presheaf map
`U ↦ 𝒮_Y(U)⁻¹ F(U)` into `f_* 𝒦_X(f^* F)`. -/
def pullbackMeromorphicSectionPresheafMap_app {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) (V : (smallEtaleSite Y)ᵒᵖ) :
    (meromorphicSectionPresheaf Y F).presheaf.obj V ⟶
      ((sheafPushforwardAbelian f).obj
          ((SheafOfModules.toSheaf _).obj
            (meromorphicSectionSheaf X ((Modules.pullback f).obj F)))).obj.obj V :=
  limit.lift _ (pullbackMeromorphicSectionCone F V.unop) ≫
    ((smallEtaleInclusion X).op.ranObjObjIsoLimit
        ((SheafOfModules.toSheaf _).obj
            (meromorphicSectionSheaf X ((Modules.pullback f).obj F))).obj
        (op ((etaleBaseChange f).obj V.unop))).inv

/-- `pullbackMeromorphicSectionPresheafMap_app` is the cone/limit/Ran component of meromorphic
pullback. -/
theorem pullbackMeromorphicSectionPresheafMap_app_eq {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) (V : (smallEtaleSite Y)ᵒᵖ) :
    pullbackMeromorphicSectionPresheafMap_app F V =
      limit.lift _ (pullbackMeromorphicSectionCone F V.unop) ≫
        ((smallEtaleInclusion X).op.ranObjObjIsoLimit
            ((SheafOfModules.toSheaf _).obj
                (meromorphicSectionSheaf X ((Modules.pullback f).obj F))).obj
            (op ((etaleBaseChange f).obj V.unop))).inv :=
  sorry

/-- The morphism from the meromorphic-section presheaf on `Y` to the pushforward of the
meromorphic-section sheaf on `X`. -/
def pullbackMeromorphicSectionPresheafMap {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) :
    (meromorphicSectionPresheaf Y F).presheaf ⟶
      ((sheafPushforwardAbelian f).obj
          ((SheafOfModules.toSheaf _).obj
            (meromorphicSectionSheaf X ((Modules.pullback f).obj F)))).obj where
  app := pullbackMeromorphicSectionPresheafMap_app F
  naturality := fun _ _ _ ↦ sorry

/-- The sheaf morphism `𝒦_Y(F) ⟶ f_* 𝒦_X(f^* F)` of abelian sheaves. -/
def pullbackMeromorphicSectionSheafHom {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) :
    (SheafOfModules.toSheaf _).obj (meromorphicSectionSheaf Y F) ⟶
      (sheafPushforwardAbelian f).obj
        ((SheafOfModules.toSheaf _).obj
          (meromorphicSectionSheaf X ((Modules.pullback f).obj F))) :=
  (sheafificationAdjunction (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).homEquiv _ _ |>.symm
    (pullbackMeromorphicSectionPresheafMap F)

/-- The type-valued sheaf morphism underlying `pullbackMeromorphicSectionSheafHom`. -/
def pullbackMeromorphicSectionTypeSheafHom {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) :
    meromorphicSectionTypeSheaf Y F ⟶
      (sheafPushforwardType f).obj
        (meromorphicSectionTypeSheaf X ((Modules.pullback f).obj F)) :=
  (sheafCompose (smallEtaleTopology Y) (forget AddCommGrpCat.{u + 1})).map
      (pullbackMeromorphicSectionSheafHom F) ≫
    (sheafPushforwardAbelianForgetIso f).hom.app
      ((SheafOfModules.toSheaf _).obj
        (meromorphicSectionSheaf X ((Modules.pullback f).obj F)))

/-- Applying `pullbackMeromorphicSectionTypeSheafHom` forgets the abelian sheaf map and
transports along the coefficient comparison. -/
theorem pullbackMeromorphicSectionTypeSheafHom_eq {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) :
    pullbackMeromorphicSectionTypeSheafHom F =
      (sheafCompose (smallEtaleTopology Y) (forget AddCommGrpCat.{u + 1})).map
          (pullbackMeromorphicSectionSheafHom F) ≫
        (sheafPushforwardAbelianForgetIso f).hom.app
          ((SheafOfModules.toSheaf _).obj
            (meromorphicSectionSheaf X ((Modules.pullback f).obj F))) :=
  sorry

/-- The canonical pullback map on meromorphic sections of a module sheaf. -/
def pullbackMeromorphicSectionMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) :
    meromorphicSections Y F →
      meromorphicSections X ((Modules.pullback f).obj F) :=
  MeromorphicConstruction.Pullback.pullback f F

/-- `pullbackMeromorphicSectionMap` is the global-sections map of
`pullbackMeromorphicSectionTypeSheafHom` transported along `Γ(f_* G) ≅ Γ(G)`. -/
theorem pullbackMeromorphicSectionMap_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules)
    (s : meromorphicSections Y F) :
    pullbackMeromorphicSectionMap f F s =
      (morphismOfTopoiSucc f).pushforwardSectionsEquiv
          (meromorphicSectionTypeSheaf X ((Modules.pullback f).obj F))
        ((Functor.sectionsFunctor _).map (pullbackMeromorphicSectionTypeSheafHom F).hom s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
