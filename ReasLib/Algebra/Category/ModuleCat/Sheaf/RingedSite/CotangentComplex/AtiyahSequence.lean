/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Evaluation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Simplicial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.AtiyahExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Simplicial.Assembly
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SimplicialAugmentation

/-!
# Simplicial first principal-parts sequence along a standard resolution

For a homomorphism of ring sheaves `φ : A ⟶ B` and a `B`-module sheaf `F`, this module assembles
the degreewise first principal-parts extensions of `F` along the standard resolution `P_• ⟶ B`
into a short complex of simplicial `P_•`-modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite.PrincipalParts
open CategoryTheory.SimplicialSite
open scoped Simplicial

noncomputable section

-- Coherence lemmas remain private implementation details of the exposed assembly.
set_option backward.privateInPublic true

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [GrothendieckTopology.HasSheafCompose (SimplicialSite.topology J)
    (forget₂ CommRingCat.{u} RingCat.{u})]
variable {A B : Sheaf J CommRingCat.{u}}

/-- The underlying simplicial ring sheaf of the standard resolution of `B` over `A`. -/
def standardSimplicial (φ : A ⟶ B) :
    SimplicialObject (Sheaf J CommRingCat.{u}) :=
  (standardResolution A (Under.mk φ)).left ⋙ Under.forget A

/-- A degree of `standardSimplicial φ` is the underlying ring sheaf of the corresponding
standard-resolution term. -/
theorem standardSimplicial_obj (φ : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    (standardSimplicial φ).obj n = (standardTerm A (Under.mk φ) n).right :=
  rfl

/-- The standard-resolution augmentation is natural in simplex operators. -/
private theorem augmentation_naturality (φ : A ⟶ B)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (standardSimplicial φ).map f ≫ standardAugmentation A (Under.mk φ) m =
      standardAugmentation A (Under.mk φ) n ≫
        ((SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B).map f :=
by
  exact congrArg (fun k => k.right)
    ((standardResolution A (Under.mk φ)).hom.naturality f)

/-- The augmentation `P_• ⟶ B` of the standard resolution, as a map of simplicial ring sheaves. -/
def augmentation (φ : A ⟶ B) :
    standardSimplicial φ ⟶ (SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B where
  app n := standardAugmentation A (Under.mk φ) n
  naturality := fun {n m} f => augmentation_naturality φ (n := n) (m := m) f

/-- A component of `augmentation φ` is the standard-resolution augmentation in that degree. -/
theorem augmentation_app (φ : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    (augmentation φ).app n = standardAugmentation A (Under.mk φ) n :=
  rfl

/-- A simplicial operator of `standardSimplicial` is the underlying map of the corresponding
standard-resolution operator. -/
theorem standardSimplicial_map (φ : A ⟶ B) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (standardSimplicial φ).map f = (standardMap A (Under.mk φ) f).right :=
  rfl

/-- The ring-square of a simplicial operator of the standard resolution. -/
theorem standardOperator_commSq (φ : A ⟶ B) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    CommSq (𝟙 A) (standardTerm A (Under.mk φ) n).hom
      (standardTerm A (Under.mk φ) m).hom ((standardSimplicial φ).map f) := by
  refine ⟨?_⟩
  simpa [standardSimplicial, standardSimplicial_map] using
    (standardMap A (Under.mk φ) f).w.symm

/-- Every standard-resolution augmentation is locally surjective on the underlying rings. -/
instance standardAugmentation_isLocallySurjective (φ : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    Presheaf.IsLocallySurjective J
      (ringSheafMap ((augmentation φ).app n)).hom := by
  apply Presheaf.isLocallySurjective_of_surjective J
  intro U y
  refine ⟨((Adjunction.SimplicialResolution.postcompose.eval.inverse
    (freeForgetAdjunction A) (Under.mk φ)).app n).hom.app U y, ?_⟩
  have h := congr_app
    (Adjunction.SimplicialResolution.postcompose.eval.inverse.comp_hom
      (freeForgetAdjunction A) (Under.mk φ)) n
  have hU := congrArg (fun k => k.hom.app U) h
  have hy := ConcreteCategory.congr_hom hU y
  exact hy

/-- The standard-resolution augmentation induces a quasi-isomorphism of additive complexes. -/
theorem augmentation_quasiIso (φ : A ⟶ B) :
    HomologicalComplex.quasiIso _ _
      (CategoryTheory.SimplicialSite.Derived.augmentationComplexMap (augmentation φ)) :=
  sorry

variable (φ : A ⟶ B) (F : ringedSiteModuleCategory J B)

/-- Restriction of `F` along a standard-resolution augmentation, as a module over that degree. -/
def restrictedDegree (n : SimplexCategoryᵒᵖ) :
    ringedSiteModuleCategory J ((standardSimplicial φ).obj n) :=
  (restrictionAlong ((augmentation φ).app n)).obj F

/-- The simplicial-operator comparison of restricted copies of `F`. -/
def restrictedModuleMap (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m) :
    restrictedDegree φ F n ⟶
      (restrictionAlong ((standardSimplicial φ).map f)).obj (restrictedDegree φ F m) :=
  (SheafOfModules.Restriction.compInvNatTrans'
      (ringSheafMap ((standardSimplicial φ).map f))
      (ringSheafMap ((augmentation φ).app m))
      (ringSheafMap ((augmentation φ).app n))
      (standardMap_comp_augmentation_ringSheaf A (Under.mk φ) f)).app F

/-- The first principal-parts sequence in a fixed degree of the standard resolution. -/
def degreeSequence (n : SimplexCategoryᵒᵖ) :
    ShortComplex (ringedSiteModuleCategory J ((standardSimplicial φ).obj n)) :=
  FirstOrder.sequence (standardTerm A (Under.mk φ) n).hom (restrictedDegree φ F n)

/-- The degree-`n` first principal-parts sequence along the standard resolution agrees with
the ℕ-indexed Atiyah extension sequence. -/
theorem degreeSequence_eq_atiyahExtension (n : ℕ) :
    degreeSequence φ F (op ⦋n⦌) = AtiyahExtension.sequence (Under.mk φ) F n :=
  rfl

/-- The base-change map of first principal-parts sequences along a simplicial operator. -/
def degreeSequenceMap (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m) :
    degreeSequence φ F n ⟶
      (degreeSequence φ F m).map (restrictionAlong ((standardSimplicial φ).map f)) :=
  FirstOrder.BaseChange.sequenceMap (standardOperator_commSq φ f) (restrictedModuleMap φ F n m f)

/-- Identity coherence of the restrictedAssembly transition maps. -/
private theorem restrictedAssembly_id (X : (SimplexCategory × C)ᵒᵖ)
    (x : ((restrictedDegree φ F) (op X.unop.1)).val.obj (op X.unop.2)) :
    (ofDegreewiseMap (standardSimplicial φ) (restrictedDegree φ F) (restrictedModuleMap φ F) (𝟙 X)).hom x = x := by
  change (F.val.map (𝟙 (op X.unop.2))).hom x = x
  rw [F.val.map_id]
  rfl

/-- Composition coherence from augmentation and principal-parts functoriality. -/
private theorem restrictedAssembly_comp :
    degreewiseMapComp (standardSimplicial φ) (restrictedDegree φ F) (restrictedModuleMap φ F) := by
  unfold degreewiseMapComp
  intro X Y Z f g x
  change (F.val.map (f.unop.2.op ≫ g.unop.2.op)).hom x =
    (F.val.map g.unop.2.op).hom ((F.val.map f.unop.2.op).hom x)
  exact F.val.map_comp_apply _ _ x

/-- Identity coherence of the cotangentAssembly transition maps. -/
private theorem cotangentAssembly_id (X : (SimplexCategory × C)ᵒᵖ)
    (x : (((fun n ↦ (degreeSequence φ F n).X₁)) (op X.unop.1)).val.obj (op X.unop.2)) :
    (ofDegreewiseMap (standardSimplicial φ) ((fun n ↦ (degreeSequence φ F n).X₁)) ((fun n m f ↦ (degreeSequenceMap φ F n m f).τ₁)) (𝟙 X)).hom x = x :=
  sorry

/-- Composition coherence from augmentation and principal-parts functoriality. -/
private theorem cotangentAssembly_comp :
    degreewiseMapComp (standardSimplicial φ) ((fun n ↦ (degreeSequence φ F n).X₁)) ((fun n m f ↦ (degreeSequenceMap φ F n m f).τ₁)) :=
  sorry

/-- Identity coherence of the principalPartsAssembly transition maps. -/
private theorem principalPartsAssembly_id (X : (SimplexCategory × C)ᵒᵖ)
    (x : (((fun n ↦ (degreeSequence φ F n).X₂)) (op X.unop.1)).val.obj (op X.unop.2)) :
    (ofDegreewiseMap (standardSimplicial φ) ((fun n ↦ (degreeSequence φ F n).X₂)) ((fun n m f ↦ (degreeSequenceMap φ F n m f).τ₂)) (𝟙 X)).hom x = x :=
  sorry

/-- Composition coherence from augmentation and principal-parts functoriality. -/
private theorem principalPartsAssembly_comp :
    degreewiseMapComp (standardSimplicial φ) ((fun n ↦ (degreeSequence φ F n).X₂)) ((fun n m f ↦ (degreeSequenceMap φ F n m f).τ₂)) :=
  sorry


/-- `F`, restricted degreewise along `P_• ⟶ B` and assembled as a simplicial `P_•`-module. -/
def restrictedModule : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ) :=
  ofDegreewise (standardSimplicial φ) (fun n ↦ restrictedDegree φ F n)
    (fun n m f ↦ restrictedModuleMap φ F n m f)
    (restrictedAssembly_id φ F) (restrictedAssembly_comp φ F)

/-- The simplicial `P_•`-module `Ω_{P_•/A} ⊗_{P_•} F`. -/
def cotangentModule : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ) :=
  ofDegreewise (standardSimplicial φ) (fun n ↦ (degreeSequence φ F n).X₁)
    (fun n m f ↦ (degreeSequenceMap φ F n m f).τ₁)
    (cotangentAssembly_id φ F) (cotangentAssembly_comp φ F)

/-- The simplicial `P_•`-module `P¹_{P_•/A}(F)`. -/
def principalPartsModule : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ) :=
  ofDegreewise (standardSimplicial φ) (fun n ↦ (degreeSequence φ F n).X₂)
    (fun n m f ↦ (degreeSequenceMap φ F n m f).τ₂)
    (principalPartsAssembly_id φ F) (principalPartsAssembly_comp φ F)

/-- The degreewise first-map component of the principal-parts sequence. -/
private def atiyahSequence_f_component (X : (SimplexCategory × C)ᵒᵖ) :
    (cotangentModule φ F).val.obj X ⟶ (principalPartsModule φ F).val.obj X :=
  ((degreeSequence φ F (op X.unop.1)).f).val.app (op X.unop.2)

/-- Compatibility of the f components with transition maps. -/
private theorem atiyahSequence_f_naturality {X Y : (SimplexCategory × C)ᵒᵖ}
    (f : X ⟶ Y) (x : (cotangentModule φ F).val.obj X) :
    (atiyahSequence_f_component φ F Y).hom ((cotangentModule φ F).val.map f |>.hom <| x) =
      ((principalPartsModule φ F).val.map f).hom ((atiyahSequence_f_component φ F X).hom x) := by
  have h := congrArg (fun k => k.val.app (op Y.unop.2))
    (degreeSequenceMap φ F (op X.unop.1) (op Y.unop.1) f.unop.1.op).comm₁₂
  have hx := ConcreteCategory.congr_hom h
    (((degreeSequence φ F (op X.unop.1)).X₁.val.map f.unop.2.op).hom x)
  exact hx.trans (congrArg
    ((degreeSequenceMap φ F (op X.unop.1) (op Y.unop.1) f.unop.1.op).τ₂.val.app
      (op Y.unop.2)).hom
    (PresheafOfModules.naturality_apply (degreeSequence φ F (op X.unop.1)).f.val
      f.unop.2.op x))

/-- The coherent assembled f arrow of the simplicial principal-parts sequence. -/
def atiyahSequence_f : cotangentModule φ F ⟶ principalPartsModule φ F :=
  ofDegreewiseHom (standardSimplicial φ) (cotangentModule φ F) (principalPartsModule φ F)
    (atiyahSequence_f_component φ F) (atiyahSequence_f_naturality φ F)

/-- The degreewise quotient-map component of the principal-parts sequence. -/
private def atiyahSequence_g_component (X : (SimplexCategory × C)ᵒᵖ) :
    (principalPartsModule φ F).val.obj X ⟶ (restrictedModule φ F).val.obj X :=
  ((degreeSequence φ F (op X.unop.1)).g).val.app (op X.unop.2)

/-- Compatibility of the g components with transition maps. -/
private theorem atiyahSequence_g_naturality {X Y : (SimplexCategory × C)ᵒᵖ}
    (f : X ⟶ Y) (x : (principalPartsModule φ F).val.obj X) :
    (atiyahSequence_g_component φ F Y).hom ((principalPartsModule φ F).val.map f |>.hom <| x) =
      ((restrictedModule φ F).val.map f).hom ((atiyahSequence_g_component φ F X).hom x) := by
  have h := congrArg (fun k => k.val.app (op Y.unop.2))
    (degreeSequenceMap φ F (op X.unop.1) (op Y.unop.1) f.unop.1.op).comm₂₃
  have hx := ConcreteCategory.congr_hom h
    (((degreeSequence φ F (op X.unop.1)).X₂.val.map f.unop.2.op).hom x)
  exact hx.trans (congrArg
    ((degreeSequenceMap φ F (op X.unop.1) (op Y.unop.1) f.unop.1.op).τ₃.val.app
      (op Y.unop.2)).hom
    (PresheafOfModules.naturality_apply (degreeSequence φ F (op X.unop.1)).g.val
      f.unop.2.op x))

/-- The coherent assembled g arrow of the simplicial principal-parts sequence. -/
def atiyahSequence_g : principalPartsModule φ F ⟶ restrictedModule φ F :=
  ofDegreewiseHom (standardSimplicial φ) (principalPartsModule φ F) (restrictedModule φ F)
    (atiyahSequence_g_component φ F) (atiyahSequence_g_naturality φ F)

/-- The two assembled principal-parts arrows compose to zero. -/
theorem atiyahSequence_zero : atiyahSequence_f φ F ≫ atiyahSequence_g φ F = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  exact congrArg (fun k => k.val.app (op X.unop.2))
    (degreeSequence φ F (op X.unop.1)).zero

/-- The short complex of simplicial `P_•`-modules
`Ω_{P_•/A} ⊗ F ⟶ P¹_{P_•/A}(F) ⟶ F`. -/
def atiyahSequence :
    ShortComplex (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) :=
  ShortComplex.mk (atiyahSequence_f φ F) (atiyahSequence_g φ F) (atiyahSequence_zero φ F)

/-- The left term of `atiyahSequence` is the assembled cotangent module. -/
theorem atiyahSequence_X₁ : (atiyahSequence φ F).X₁ = cotangentModule φ F :=
  rfl

/-- The middle term of `atiyahSequence` is the assembled first principal-parts module. -/
theorem atiyahSequence_X₂ : (atiyahSequence φ F).X₂ = principalPartsModule φ F :=
  rfl

/-- The right term of `atiyahSequence` is the assembled restriction of `F`. -/
theorem atiyahSequence_X₃ : (atiyahSequence φ F).X₃ = restrictedModule φ F :=
  rfl

/-- The simplicial first principal-parts sequence is short exact. -/
theorem atiyahSequence_shortExact [HasSheafify J AddCommGrpCat.{u}] :
    (atiyahSequence φ F).ShortExact :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
