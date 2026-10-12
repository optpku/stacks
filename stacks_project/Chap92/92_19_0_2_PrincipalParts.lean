/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Simplicial
public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import stacks_project.Chap92.«92_19_0_1_Extension»

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
open scoped Simplicial

noncomputable section

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

/-- Unfolding of `standardSimplicial` as the forgetful image of the standard resolution. -/
theorem standardSimplicial_eq (φ : A ⟶ B) :
    standardSimplicial φ =
      (standardResolution A (Under.mk φ)).left ⋙ Under.forget A :=
  sorry

/-- A degree of `standardSimplicial φ` is the underlying ring sheaf of the corresponding
standard-resolution term. -/
theorem standardSimplicial_obj (φ : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    (standardSimplicial φ).obj n = (standardTerm A (Under.mk φ) n).right :=
  sorry

/-- The augmentation `P_• ⟶ B` of the standard resolution, as a map of simplicial ring sheaves. -/
def augmentation (φ : A ⟶ B) :
    standardSimplicial φ ⟶ (SimplicialObject.const (Sheaf J CommRingCat.{u})).obj B where
  app n := standardAugmentation A (Under.mk φ) n
  naturality := sorry

/-- A component of `augmentation φ` is the standard-resolution augmentation in that degree. -/
theorem augmentation_app (φ : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    (augmentation φ).app n = standardAugmentation A (Under.mk φ) n :=
  sorry

/-- A simplicial operator of `standardSimplicial` is the underlying map of the corresponding
standard-resolution operator. -/
theorem standardSimplicial_map (φ : A ⟶ B) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (standardSimplicial φ).map f = (standardMap A (Under.mk φ) f).right :=
  sorry

/-- Restriction along a simplicial operator of `standardSimplicial` followed by the
augmentation agrees with restriction along the augmentation in the source degree. -/
theorem standardSimplicial_map_comp_augmentation_ringSheaf
    (φ : A ⟶ B) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ringSheafMap ((augmentation φ).app n) =
      ringSheafMap ((standardSimplicial φ).map f) ≫
        ringSheafMap ((augmentation φ).app m) :=
  sorry

/-- The ring-square of a simplicial operator of the standard resolution. -/
theorem standardOperator_commSq (φ : A ⟶ B) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    CommSq (𝟙 A) (standardTerm A (Under.mk φ) n).hom
      (standardTerm A (Under.mk φ) m).hom ((standardSimplicial φ).map f) :=
  sorry

/-- Restriction maps for a degreewise family of modules over a simplicial ring sheaf, as maps of
modules on the simplicial site. -/
def ofDegreewiseMap (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) :
    (objFamily (op X.unop.1)).val.obj (op X.unop.2) ⟶
      (ModuleCat.restrictScalars
        ((CategoryTheory.Sheaf.ringSheafOfComm (SimplicialSite.ringSheaf 𝒪)).obj.map f).hom).obj
        ((objFamily (op Y.unop.1)).val.obj (op Y.unop.2)) :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom
      (AddMonoidHom.mk'
        (fun t ↦
          ((mapFamily (op X.unop.1) (op Y.unop.1) f.unop.1.op).val.app (op Y.unop.2)).hom
            (((objFamily (op X.unop.1)).val.map f.unop.2.op).hom t))
        sorry))
    sorry

/-- Composition coherence of the assembled transition maps, kept as an explicit
predicate so specializing it does not expose private simplex-code implementation terms. -/
@[irreducible] def degreewiseMapComp (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m)) : Prop :=
  ∀ {X Y Z : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
    (ofDegreewiseMap 𝒪 objFamily mapFamily (f ≫ g)).hom x =
      (ofDegreewiseMap 𝒪 objFamily mapFamily g).hom
        ((ofDegreewiseMap 𝒪 objFamily mapFamily f).hom x)

/-- Apply the composition-coherence predicate to specified composable site arrows. -/
theorem degreewiseMapComp_apply (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (h : degreewiseMapComp 𝒪 objFamily mapFamily)
    {X Y Z : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)) :
    (ofDegreewiseMap 𝒪 objFamily mapFamily (f ≫ g)).hom x =
      (ofDegreewiseMap 𝒪 objFamily mapFamily g).hom
        ((ofDegreewiseMap 𝒪 objFamily mapFamily f).hom x) := by
  unfold degreewiseMapComp at h
  exact h f g x

/-- Assemble a coherent degreewise family into a module on the simplicial site.
Identity and composition must hold for the actual assembled maps. -/
def ofDegreewise (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (hId : ∀ (X : (SimplexCategory × C)ᵒᵖ)
      (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
      (ofDegreewiseMap 𝒪 objFamily mapFamily (𝟙 X)).hom x = x)
    (hComp : degreewiseMapComp 𝒪 objFamily mapFamily) :
    SimplicialSite.ModuleCat (J := J) 𝒪 where
  val :=
    { obj := fun X ↦ (objFamily (op X.unop.1)).val.obj (op X.unop.2)
      map := fun f ↦ ofDegreewiseMap 𝒪 objFamily mapFamily f
      map_id := by
        intro X
        ext x
        exact hId X x
      map_comp := by
        intro X Y Z f g
        ext x
        exact degreewiseMapComp_apply 𝒪 objFamily mapFamily hComp f g x }
  isSheaf := sorry

/-- An assembled coherent module has the specified degreewise objects. -/
theorem ofDegreewise_obj (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (hId : ∀ (X : (SimplexCategory × C)ᵒᵖ)
      (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
      (ofDegreewiseMap 𝒪 objFamily mapFamily (𝟙 X)).hom x = x)
    (hComp : degreewiseMapComp 𝒪 objFamily mapFamily)
    (X : (SimplexCategory × C)ᵒᵖ) :
    (ofDegreewise 𝒪 objFamily mapFamily hId hComp).val.obj X =
      (objFamily (op X.unop.1)).val.obj (op X.unop.2) := rfl

/-- An assembled coherent module has the specified transition maps. -/
theorem ofDegreewise_map (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (objFamily : ∀ n : SimplexCategoryᵒᵖ, ringedSiteModuleCategory J (𝒪.obj n))
    (mapFamily : ∀ (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m),
      objFamily n ⟶ (restrictionAlong (𝒪.map f)).obj (objFamily m))
    (hId : ∀ (X : (SimplexCategory × C)ᵒᵖ)
      (x : (objFamily (op X.unop.1)).val.obj (op X.unop.2)),
      (ofDegreewiseMap 𝒪 objFamily mapFamily (𝟙 X)).hom x = x)
    (hComp : degreewiseMapComp 𝒪 objFamily mapFamily)
    {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) :
    (ofDegreewise 𝒪 objFamily mapFamily hId hComp).val.map f =
      ofDegreewiseMap 𝒪 objFamily mapFamily f := rfl

/-- A compatible component family between already assembled modules defines a morphism.
The domain and codomain already contain their identity/composition laws. -/
def ofDegreewiseHom (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (M N : SimplicialSite.ModuleCat (J := J) 𝒪)
    (α : ∀ X : (SimplexCategory × C)ᵒᵖ, M.val.obj X ⟶ N.val.obj X)
    (hα : ∀ {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X),
      (α Y).hom ((M.val.map f).hom x) = (N.val.map f).hom ((α X).hom x)) : M ⟶ N where
  val :=
    { app := α
      naturality := by
        intro X Y f
        ext x
        exact hα f x }

/-- The coherent assembled morphism has exactly the specified components. -/
theorem ofDegreewiseHom_app (𝒪 : SimplicialObject (Sheaf J CommRingCat.{u}))
    (M N : SimplicialSite.ModuleCat (J := J) 𝒪)
    (α : ∀ X : (SimplexCategory × C)ᵒᵖ, M.val.obj X ⟶ N.val.obj X)
    (hα : ∀ {X Y : (SimplexCategory × C)ᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X),
      (α Y).hom ((M.val.map f).hom x) = (N.val.map f).hom ((α X).hom x))
    (X : (SimplexCategory × C)ᵒᵖ) :
    (ofDegreewiseHom 𝒪 M N α hα).val.app X = α X := rfl

variable (φ : A ⟶ B) (F : ringedSiteModuleCategory J B)

/-- Restriction of `F` along a standard-resolution augmentation, as a module over that degree. -/
def restrictedDegree (n : SimplexCategoryᵒᵖ) :
    ringedSiteModuleCategory J ((standardSimplicial φ).obj n) :=
  (restrictionAlong ((augmentation φ).app n)).obj F

/-- Unfolding of `restrictedDegree` as restriction of scalars along the augmentation. -/
theorem restrictedDegree_eq (n : SimplexCategoryᵒᵖ) :
    restrictedDegree φ F n = (restrictionAlong ((augmentation φ).app n)).obj F :=
  sorry

/-- The simplicial-operator comparison of restricted copies of `F`. -/
def restrictedModuleMap (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m) :
    restrictedDegree φ F n ⟶
      (restrictionAlong ((standardSimplicial φ).map f)).obj (restrictedDegree φ F m) :=
  (SheafOfModules.Restriction.compInvNatTrans'
      (ringSheafMap ((standardSimplicial φ).map f))
      (ringSheafMap ((augmentation φ).app m))
      (ringSheafMap ((augmentation φ).app n))
      (standardSimplicial_map_comp_augmentation_ringSheaf φ f)).app F

/-- Unfolding of `restrictedModuleMap` as the inverse composition-restriction comparison. -/
theorem restrictedModuleMap_eq (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m) :
    restrictedModuleMap φ F n m f =
      (SheafOfModules.Restriction.compInvNatTrans'
          (ringSheafMap ((standardSimplicial φ).map f))
          (ringSheafMap ((augmentation φ).app m))
          (ringSheafMap ((augmentation φ).app n))
          (standardSimplicial_map_comp_augmentation_ringSheaf φ f)).app F :=
  sorry

/-- The first principal-parts sequence in a fixed degree of the standard resolution. -/
def degreeSequence (n : SimplexCategoryᵒᵖ) :
    ShortComplex (ringedSiteModuleCategory J ((standardSimplicial φ).obj n)) :=
  FirstOrder.sequence (standardTerm A (Under.mk φ) n).hom (restrictedDegree φ F n)

/-- Unfolding of `degreeSequence` as the canonical first principal-parts sequence. -/
theorem degreeSequence_eq (n : SimplexCategoryᵒᵖ) :
    degreeSequence φ F n =
      FirstOrder.sequence (standardTerm A (Under.mk φ) n).hom (restrictedDegree φ F n) :=
  sorry

/-- The degree-`n` first principal-parts sequence along the standard resolution agrees with
the ℕ-indexed Atiyah extension sequence. -/
theorem degreeSequence_eq_atiyahExtension (n : ℕ) :
    degreeSequence φ F (op ⦋n⦌) = AtiyahExtension.sequence (Under.mk φ) F n :=
  sorry

/-- The base-change map of first principal-parts sequences along a simplicial operator. -/
def degreeSequenceMap (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m) :
    degreeSequence φ F n ⟶
      (degreeSequence φ F m).map (restrictionAlong ((standardSimplicial φ).map f)) :=
  FirstOrder.BaseChange.sequenceMap (standardOperator_commSq φ f) (restrictedModuleMap φ F n m f)

/-- Unfolding of `degreeSequenceMap` as principal-parts base change. -/
theorem degreeSequenceMap_eq (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m) :
    degreeSequenceMap φ F n m f =
      FirstOrder.BaseChange.sequenceMap (standardOperator_commSq φ f)
        (restrictedModuleMap φ F n m f) :=
  sorry

/-- Identity coherence of the source-specific restrictedAssembly transition maps. -/
theorem restrictedAssembly_id (X : (SimplexCategory × C)ᵒᵖ)
    (x : ((restrictedDegree φ F) (op X.unop.1)).val.obj (op X.unop.2)) :
    (ofDegreewiseMap (standardSimplicial φ) (restrictedDegree φ F) (restrictedModuleMap φ F) (𝟙 X)).hom x = x :=
  sorry

/-- Composition coherence from augmentation and principal-parts functoriality. -/
theorem restrictedAssembly_comp :
    degreewiseMapComp (standardSimplicial φ) (restrictedDegree φ F) (restrictedModuleMap φ F) :=
  sorry

/-- Identity coherence of the source-specific cotangentAssembly transition maps. -/
theorem cotangentAssembly_id (X : (SimplexCategory × C)ᵒᵖ)
    (x : (((fun n ↦ (degreeSequence φ F n).X₁)) (op X.unop.1)).val.obj (op X.unop.2)) :
    (ofDegreewiseMap (standardSimplicial φ) ((fun n ↦ (degreeSequence φ F n).X₁)) ((fun n m f ↦ (degreeSequenceMap φ F n m f).τ₁)) (𝟙 X)).hom x = x :=
  sorry

/-- Composition coherence from augmentation and principal-parts functoriality. -/
theorem cotangentAssembly_comp :
    degreewiseMapComp (standardSimplicial φ) ((fun n ↦ (degreeSequence φ F n).X₁)) ((fun n m f ↦ (degreeSequenceMap φ F n m f).τ₁)) :=
  sorry

/-- Identity coherence of the source-specific principalPartsAssembly transition maps. -/
theorem principalPartsAssembly_id (X : (SimplexCategory × C)ᵒᵖ)
    (x : (((fun n ↦ (degreeSequence φ F n).X₂)) (op X.unop.1)).val.obj (op X.unop.2)) :
    (ofDegreewiseMap (standardSimplicial φ) ((fun n ↦ (degreeSequence φ F n).X₂)) ((fun n m f ↦ (degreeSequenceMap φ F n m f).τ₂)) (𝟙 X)).hom x = x :=
  sorry

/-- Composition coherence from augmentation and principal-parts functoriality. -/
theorem principalPartsAssembly_comp :
    degreewiseMapComp (standardSimplicial φ) ((fun n ↦ (degreeSequence φ F n).X₂)) ((fun n m f ↦ (degreeSequenceMap φ F n m f).τ₂)) :=
  sorry


/-- `F`, restricted degreewise along `P_• ⟶ B` and assembled as a simplicial `P_•`-module. -/
def restrictedModule : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ) :=
  ofDegreewise (standardSimplicial φ) (fun n ↦ restrictedDegree φ F n)
    (fun n m f ↦ restrictedModuleMap φ F n m f)
    (restrictedAssembly_id φ F) (restrictedAssembly_comp φ F)

/-- Unfolding of `restrictedModule` as an `ofDegreewise` assembly. -/
theorem restrictedModule_eq :
    restrictedModule φ F =
      ofDegreewise (standardSimplicial φ) (fun n ↦ restrictedDegree φ F n)
        (fun n m f ↦ restrictedModuleMap φ F n m f)
        (restrictedAssembly_id φ F) (restrictedAssembly_comp φ F) :=
  sorry

/-- The simplicial `P_•`-module `Ω_{P_•/A} ⊗_{P_•} F`. -/
def cotangentModule : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ) :=
  ofDegreewise (standardSimplicial φ) (fun n ↦ (degreeSequence φ F n).X₁)
    (fun n m f ↦ (degreeSequenceMap φ F n m f).τ₁)
    (cotangentAssembly_id φ F) (cotangentAssembly_comp φ F)

/-- Unfolding of `cotangentModule` as an `ofDegreewise` assembly of cotangent tensors. -/
theorem cotangentModule_eq :
    cotangentModule φ F =
      ofDegreewise (standardSimplicial φ) (fun n ↦ (degreeSequence φ F n).X₁)
        (fun n m f ↦ (degreeSequenceMap φ F n m f).τ₁)
        (cotangentAssembly_id φ F) (cotangentAssembly_comp φ F) :=
  sorry

/-- The simplicial `P_•`-module `P¹_{P_•/A}(F)`. -/
def principalPartsModule : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ) :=
  ofDegreewise (standardSimplicial φ) (fun n ↦ (degreeSequence φ F n).X₂)
    (fun n m f ↦ (degreeSequenceMap φ F n m f).τ₂)
    (principalPartsAssembly_id φ F) (principalPartsAssembly_comp φ F)

/-- Unfolding of `principalPartsModule` as an `ofDegreewise` assembly of first principal parts. -/
theorem principalPartsModule_eq :
    principalPartsModule φ F =
      ofDegreewise (standardSimplicial φ) (fun n ↦ (degreeSequence φ F n).X₂)
        (fun n m f ↦ (degreeSequenceMap φ F n m f).τ₂)
        (principalPartsAssembly_id φ F) (principalPartsAssembly_comp φ F) :=
  sorry

/-- The actual degreewise f component of the principal-parts sequence. -/
def atiyahSequence_f_component (X : (SimplexCategory × C)ᵒᵖ) :
    (cotangentModule φ F).val.obj X ⟶ (principalPartsModule φ F).val.obj X :=
  ((degreeSequence φ F (op X.unop.1)).f).val.app (op X.unop.2)

/-- Compatibility of the source-specific f components with transition maps. -/
theorem atiyahSequence_f_naturality {X Y : (SimplexCategory × C)ᵒᵖ}
    (f : X ⟶ Y) (x : (cotangentModule φ F).val.obj X) :
    (atiyahSequence_f_component φ F Y).hom ((cotangentModule φ F).val.map f |>.hom <| x) =
      ((principalPartsModule φ F).val.map f).hom ((atiyahSequence_f_component φ F X).hom x) :=
  sorry

/-- The coherent assembled f arrow of the simplicial principal-parts sequence. -/
def atiyahSequence_f : cotangentModule φ F ⟶ principalPartsModule φ F :=
  ofDegreewiseHom (standardSimplicial φ) (cotangentModule φ F) (principalPartsModule φ F)
    (atiyahSequence_f_component φ F) (atiyahSequence_f_naturality φ F)

/-- The assembled arrow is built from its specified compatible components. -/
theorem atiyahSequence_f_eq :
    atiyahSequence_f φ F =
      ofDegreewiseHom (standardSimplicial φ) (cotangentModule φ F) (principalPartsModule φ F)
        (atiyahSequence_f_component φ F) (atiyahSequence_f_naturality φ F) :=
  rfl

/-- The actual degreewise g component of the principal-parts sequence. -/
def atiyahSequence_g_component (X : (SimplexCategory × C)ᵒᵖ) :
    (principalPartsModule φ F).val.obj X ⟶ (restrictedModule φ F).val.obj X :=
  ((degreeSequence φ F (op X.unop.1)).g).val.app (op X.unop.2)

/-- Compatibility of the source-specific g components with transition maps. -/
theorem atiyahSequence_g_naturality {X Y : (SimplexCategory × C)ᵒᵖ}
    (f : X ⟶ Y) (x : (principalPartsModule φ F).val.obj X) :
    (atiyahSequence_g_component φ F Y).hom ((principalPartsModule φ F).val.map f |>.hom <| x) =
      ((restrictedModule φ F).val.map f).hom ((atiyahSequence_g_component φ F X).hom x) :=
  sorry

/-- The coherent assembled g arrow of the simplicial principal-parts sequence. -/
def atiyahSequence_g : principalPartsModule φ F ⟶ restrictedModule φ F :=
  ofDegreewiseHom (standardSimplicial φ) (principalPartsModule φ F) (restrictedModule φ F)
    (atiyahSequence_g_component φ F) (atiyahSequence_g_naturality φ F)

/-- The assembled arrow is built from its specified compatible components. -/
theorem atiyahSequence_g_eq :
    atiyahSequence_g φ F =
      ofDegreewiseHom (standardSimplicial φ) (principalPartsModule φ F) (restrictedModule φ F)
        (atiyahSequence_g_component φ F) (atiyahSequence_g_naturality φ F) :=
  rfl

/-- The two assembled principal-parts arrows compose to zero. -/
theorem atiyahSequence_zero : atiyahSequence_f φ F ≫ atiyahSequence_g φ F = 0 :=
  sorry

/-- The short complex of simplicial `P_•`-modules
`Ω_{P_•/A} ⊗ F ⟶ P¹_{P_•/A}(F) ⟶ F`. -/
def atiyahSequence :
    ShortComplex (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) :=
  ShortComplex.mk (atiyahSequence_f φ F) (atiyahSequence_g φ F) (atiyahSequence_zero φ F)

/-- Unfolding of `atiyahSequence` as a short complex with the assembled principal-parts arrows. -/
theorem atiyahSequence_eq :
    atiyahSequence φ F =
      ShortComplex.mk (atiyahSequence_f φ F) (atiyahSequence_g φ F) (atiyahSequence_zero φ F) :=
  sorry

/-- The left term of `atiyahSequence` is the assembled cotangent module. -/
theorem atiyahSequence_X₁ : (atiyahSequence φ F).X₁ = cotangentModule φ F :=
  sorry

/-- The middle term of `atiyahSequence` is the assembled first principal-parts module. -/
theorem atiyahSequence_X₂ : (atiyahSequence φ F).X₂ = principalPartsModule φ F :=
  sorry

/-- The right term of `atiyahSequence` is the assembled restriction of `F`. -/
theorem atiyahSequence_X₃ : (atiyahSequence φ F).X₃ = restrictedModule φ F :=
  sorry

/-- The simplicial first principal-parts sequence is short exact. -/
theorem atiyahSequence_shortExact [HasSheafify J AddCommGrpCat.{u}] :
    (atiyahSequence φ F).ShortExact :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
