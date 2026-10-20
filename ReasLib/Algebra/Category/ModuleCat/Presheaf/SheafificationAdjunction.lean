/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Adjunction API for commutative-ring module-presheaf sheafification

This leaf packages the standard module-sheafification adjunction at the
canonical map from a commutative-ring presheaf to its sheafification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite (ringSheaf ringedSiteModuleCategory)

noncomputable section

universe u v w z

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [Presheaf.IsLocallyInjective J (sheafificationRingMap J 𝒪)]
variable [Presheaf.IsLocallySurjective J (sheafificationRingMap J 𝒪)]

/-- The right adjoint to module sheafification: forget a module sheaf and restrict scalars along
the canonical ring sheafification map. -/
noncomputable abbrev moduleSheafificationRightAdjoint :
    ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪) ⥤
      PresheafOfModules.{z} (ringPresheaf 𝒪) :=
  SheafOfModules.forget.{z} (ringSheaf J (commRingSheafification J 𝒪)) ⋙
    PresheafOfModules.restrictScalars.{z} (sheafificationRingMap J 𝒪)

/-- The canonical adjunction from module presheaves to module sheaves after sheafifying the
commutative structure presheaf. -/
noncomputable abbrev moduleSheafificationAdjunction :
    moduleSheafification J 𝒪 ⊣ moduleSheafificationRightAdjoint J 𝒪 :=
  PresheafOfModules.sheafificationAdjunction.{z} (sheafificationRingMap J 𝒪)

/-- The unit of the canonical module-sheafification adjunction. -/
noncomputable abbrev moduleSheafificationUnit :
    𝟭 (PresheafOfModules.{z} (ringPresheaf 𝒪)) ⟶
      moduleSheafification J 𝒪 ⋙ moduleSheafificationRightAdjoint J 𝒪 :=
  (moduleSheafificationAdjunction J 𝒪).unit

/-- The concrete counit natural transformation of the module-sheafification adjunction. -/
@[stacks 0G3Y "module sheafification adjunction counit"]
noncomputable abbrev moduleSheafificationCounit :
    moduleSheafificationRightAdjoint J 𝒪 ⋙ moduleSheafification J 𝒪 ⟶
      𝟭 (ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪)) :=
  (moduleSheafificationAdjunction J 𝒪).counit

/-- The explicit inverse natural transformation to the module-sheafification counit. -/
@[stacks 0G3Y "module sheafification adjunction counit inverse"]
noncomputable def moduleSheafificationCounitInv :
    𝟭 (ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪)) ⟶
      moduleSheafificationRightAdjoint J 𝒪 ⋙ moduleSheafification J 𝒪 where
  app ℱ := inv ((moduleSheafificationCounit J 𝒪).app ℱ)
  naturality _ _ f := sorry

/-- The module-sheafification counit followed by its explicit inverse is the identity. -/
@[simp, stacks 0G3Y "module sheafification counit forward-inverse law"]
theorem moduleSheafificationCounit_hom_inv_id :
    moduleSheafificationCounit J 𝒪 ≫ moduleSheafificationCounitInv J 𝒪 = 𝟙 _ := sorry

/-- The explicit inverse to the module-sheafification counit followed by the counit is the
identity. -/
@[simp, stacks 0G3Y "module sheafification counit inverse-forward law"]
theorem moduleSheafificationCounit_inv_hom_id :
    moduleSheafificationCounitInv J 𝒪 ≫ moduleSheafificationCounit J 𝒪 = 𝟙 _ := sorry

/-- The counit of module sheafification is a literal natural isomorphism with an explicitly owned
inverse. -/
@[stacks 0G3Y "module sheafification counit natural isomorphism"]
noncomputable def moduleSheafificationCounitIso :
    moduleSheafificationRightAdjoint J 𝒪 ⋙ moduleSheafification J 𝒪 ≅
      𝟭 (ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪)) where
  hom := moduleSheafificationCounit J 𝒪
  inv := moduleSheafificationCounitInv J 𝒪
  hom_inv_id := moduleSheafificationCounit_hom_inv_id J 𝒪
  inv_hom_id := moduleSheafificationCounit_inv_hom_id J 𝒪

/-- The forward natural transformation of the module-sheafification counit is the adjunction
counit. -/
@[simp, stacks 0G3Y "module sheafification counit natural isomorphism hom"]
theorem moduleSheafificationCounitIso_hom :
    (moduleSheafificationCounitIso J 𝒪).hom = moduleSheafificationCounit J 𝒪 := sorry

/-- The inverse natural transformation of the module-sheafification counit is explicit. -/
@[simp, stacks 0G3Y "module sheafification counit natural isomorphism inverse"]
theorem moduleSheafificationCounitIso_inv :
    (moduleSheafificationCounitIso J 𝒪).inv = moduleSheafificationCounitInv J 𝒪 := sorry

/-- The counit identifies the sheafification of the underlying restricted presheaf of a module
sheaf with that module sheaf. -/
@[stacks 0G3Y "module sheafification counit component isomorphism"]
noncomputable abbrev moduleSheafificationCounitIsoApp
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪)) :
    (moduleSheafification J 𝒪).obj
        ((moduleSheafificationRightAdjoint J 𝒪).obj ℱ) ≅ ℱ :=
  (moduleSheafificationCounitIso J 𝒪).app ℱ

/-- The forward component of the module-sheafification counit is its concrete adjunction
counit component. -/
@[simp, stacks 0G3Y "module sheafification counit component"]
theorem moduleSheafificationCounitIso_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪)) :
    (moduleSheafificationCounitIso J 𝒪).app ℱ =
      moduleSheafificationCounitIsoApp J 𝒪 ℱ := sorry

/-- The forward component of the module-sheafification counit natural isomorphism is the named
counit component. -/
@[simp, stacks 0G3Y "module sheafification counit hom component"]
theorem moduleSheafificationCounitIso_hom_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪)) :
    (moduleSheafificationCounitIso J 𝒪).hom.app ℱ =
      (moduleSheafificationCounit J 𝒪).app ℱ := sorry

/-- The inverse component of the module-sheafification counit natural isomorphism is the named
explicit inverse component. -/
@[simp, stacks 0G3Y "module sheafification counit inverse component"]
theorem moduleSheafificationCounitIso_inv_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪)) :
    (moduleSheafificationCounitIso J 𝒪).inv.app ℱ =
      (moduleSheafificationCounitInv J 𝒪).app ℱ := sorry

/-- Forgetting the module structure after module sheafification agrees with sheafification of
the underlying additive presheaf. -/
noncomputable abbrev moduleSheafificationCompToSheaf :
    moduleSheafification J 𝒪 ⋙
        SheafOfModules.toSheaf.{z} (ringSheaf J (commRingSheafification J 𝒪)) ≅
      PresheafOfModules.toPresheaf.{z} (ringPresheaf 𝒪) ⋙
        presheafToSheaf J AddCommGrpCat.{z} :=
  PresheafOfModules.sheafificationCompToSheaf (sheafificationRingMap J 𝒪)

/-- Under strong sheafification, canonical module sheafification is exact. -/
theorem moduleSheafificationExact [HasSheafify J AddCommGrpCat.{z}] :
    exactFunctor
      (PresheafOfModules.{z} (ringPresheaf 𝒪))
      (ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪))
      (moduleSheafification J 𝒪) := sorry

namespace ModuleSheafification

variable {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (phi : 𝒪₁ ⟶ 𝒪₂)

/-- Restrict a module presheaf along `phi` and then sheafify it over the sheafification of the
source ring presheaf. -/
noncomputable abbrev restrictThenSheafify :
    PresheafOfModules.{z} (ringPresheaf 𝒪₂) ⥤
      ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪₁) :=
  PresheafOfModules.restrictScalars
      (PresheafOfModules.presheafStructureMap phi) ⋙
    moduleSheafification J 𝒪₁

/-- Sheafify a module presheaf over the target ring presheaf and then restrict scalars along the
sheafified ring map. -/
noncomputable abbrev sheafifyThenRestrict :
    PresheafOfModules.{z} (ringPresheaf 𝒪₂) ⥤
      ringedSiteModuleCategory.{u, v, z, w} J (commRingSheafification J 𝒪₁) :=
  moduleSheafification J 𝒪₂ ⋙
    SheafOfModules.RingedSite.restrictionAlong (commRingSheafificationMap J phi)

/-- The pointwise identity intertwines the two scalar actions obtained by exchanging
restriction of scalars with commutative-ring module sheafification. -/
theorem restrictAppIso_smul (F : PresheafOfModules.{z} (ringPresheaf 𝒪₂))
    (X : Cᵒᵖ) (r : (ringSheaf J (commRingSheafification J 𝒪₁)).obj.obj X) :
    (Iso.refl _).hom ≫ (((sheafifyThenRestrict J phi).obj F).val.obj X).smul r =
      (((restrictThenSheafify J phi).obj F).val.obj X).smul r ≫
        (Iso.refl _).hom := sorry

/-- The pointwise identity isomorphism between restriction before and after commutative-ring
module sheafification. -/
noncomputable def restrictAppIso
    (F : PresheafOfModules.{z} (ringPresheaf 𝒪₂)) (X : Cᵒᵖ) :
    ((restrictThenSheafify J phi).obj F).val.obj X ≅
      ((sheafifyThenRestrict J phi).obj F).val.obj X :=
  ModuleCat.isoMk (Iso.refl _) (restrictAppIso_smul J phi F X)

/-- The pointwise restriction-sheafification isomorphisms commute with restriction maps. -/
theorem restrictAppIso_naturality
    (F : PresheafOfModules.{z} (ringPresheaf 𝒪₂)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((restrictThenSheafify J phi).obj F).val.map f ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J (commRingSheafification J 𝒪₁)).obj.map f).hom)).map
          (restrictAppIso J phi F Y).hom =
      (restrictAppIso J phi F X).hom ≫
        ((sheafifyThenRestrict J phi).obj F).val.map f := sorry

/-- The module presheaves underlying restriction before and after commutative-ring module
sheafification are canonically isomorphic. -/
noncomputable def restrictPresheafIso
    (F : PresheafOfModules.{z} (ringPresheaf 𝒪₂)) :
    ((restrictThenSheafify J phi).obj F).val ≅
      ((sheafifyThenRestrict J phi).obj F).val :=
  PresheafOfModules.isoMk (restrictAppIso J phi F)
    (fun _ _ f ↦ restrictAppIso_naturality J phi F f)

/-- Restriction of scalars along a morphism of commutative-ring presheaves commutes with
canonical module sheafification. -/
@[stacks 0G3Y "restriction commutes with module sheafification"]
noncomputable def restrictIso
    (F : PresheafOfModules.{z} (ringPresheaf 𝒪₂)) :
    (restrictThenSheafify J phi).obj F ≅ (sheafifyThenRestrict J phi).obj F :=
  (SheafOfModules.fullyFaithfulForget
    (ringSheaf J (commRingSheafification J 𝒪₁))).preimageIso
      (restrictPresheafIso J phi F)

/-- The restriction-sheafification comparison is natural in the target-ring module
presheaf. -/
theorem restrictIso_naturality
    {F G : PresheafOfModules.{z} (ringPresheaf 𝒪₂)} (f : F ⟶ G) :
    (restrictThenSheafify J phi).map f ≫ (restrictIso J phi G).hom =
      (restrictIso J phi F).hom ≫ (sheafifyThenRestrict J phi).map f := sorry

/-- The forward restriction-sheafification comparison natural transformation. -/
@[stacks 0G3Y "restriction and module sheafification forward natural transformation"]
noncomputable def restrictNatTrans :
    restrictThenSheafify J phi ⟶ sheafifyThenRestrict J phi where
  app F := (restrictIso J phi F).hom
  naturality _ _ f := restrictIso_naturality J phi f

/-- The inverse restriction-sheafification comparison is natural in the target-ring module
presheaf. -/
@[stacks 0G3Y "inverse restriction and module sheafification naturality"]
theorem restrictIso_inv_naturality
    {F G : PresheafOfModules.{z} (ringPresheaf 𝒪₂)} (f : F ⟶ G) :
    (sheafifyThenRestrict J phi).map f ≫ (restrictIso J phi G).inv =
      (restrictIso J phi F).inv ≫ (restrictThenSheafify J phi).map f := sorry

/-- The inverse restriction-sheafification comparison natural transformation. -/
@[stacks 0G3Y "inverse restriction and module sheafification natural transformation"]
noncomputable def restrictInvNatTrans :
    sheafifyThenRestrict J phi ⟶ restrictThenSheafify J phi where
  app F := (restrictIso J phi F).inv
  naturality _ _ f := restrictIso_inv_naturality J phi f

/-- The forward restriction-sheafification comparison followed by its inverse is the identity. -/
@[simp, stacks 0G3Y "restriction and module sheafification forward-inverse law"]
theorem restrictNatTrans_hom_inv_id :
    restrictNatTrans J phi ≫ restrictInvNatTrans J phi = 𝟙 _ := sorry

/-- The inverse restriction-sheafification comparison followed by its forward map is the
identity. -/
@[simp, stacks 0G3Y "restriction and module sheafification inverse-forward law"]
theorem restrictNatTrans_inv_hom_id :
    restrictInvNatTrans J phi ≫ restrictNatTrans J phi = 𝟙 _ := sorry

/-- Restriction of scalars and canonical commutative-ring module sheafification commute by a
natural isomorphism. -/
@[stacks 0G3Y "restriction and module sheafification natural isomorphism"]
noncomputable def restrictNatIso :
    restrictThenSheafify J phi ≅ sheafifyThenRestrict J phi :=
  { hom := restrictNatTrans J phi
    inv := restrictInvNatTrans J phi
    hom_inv_id := restrictNatTrans_hom_inv_id J phi
    inv_hom_id := restrictNatTrans_inv_hom_id J phi }

/-- The forward natural transformation of `restrictNatIso` is the named comparison. -/
@[simp, stacks 0G3Y "restriction natural isomorphism hom"]
theorem restrictNatIso_hom :
    (restrictNatIso J phi).hom = restrictNatTrans J phi := sorry

/-- The inverse natural transformation of `restrictNatIso` is the named inverse comparison. -/
@[simp, stacks 0G3Y "restriction natural isomorphism inverse"]
theorem restrictNatIso_inv :
    (restrictNatIso J phi).inv = restrictInvNatTrans J phi := sorry

/-- A component of `restrictNatIso` is the objectwise restriction-sheafification isomorphism. -/
@[simp, stacks 0G3Y "restriction natural isomorphism component"]
theorem restrictNatIso_app
    (F : PresheafOfModules.{z} (ringPresheaf 𝒪₂)) :
    (restrictNatIso J phi).app F = restrictIso J phi F := sorry

/-- A forward component of `restrictNatIso` is the named objectwise comparison. -/
@[simp, stacks 0G3Y "restriction natural isomorphism hom component"]
theorem restrictNatIso_hom_app
    (F : PresheafOfModules.{z} (ringPresheaf 𝒪₂)) :
    (restrictNatIso J phi).hom.app F = (restrictNatTrans J phi).app F := sorry

/-- An inverse component of `restrictNatIso` is the named objectwise inverse comparison. -/
@[simp, stacks 0G3Y "restriction natural isomorphism inverse component"]
theorem restrictNatIso_inv_app
    (F : PresheafOfModules.{z} (ringPresheaf 𝒪₂)) :
    (restrictNatIso J phi).inv.app F = (restrictInvNatTrans J phi).app F := sorry

/-- Sheafify a morphism which is linear only after restriction along a morphism of
commutative-ring presheaves. -/
@[stacks 0G3Y "sheafification after restriction of scalars"]
noncomputable def mapAfterRestriction
    {F G : PresheafOfModules.{z} (ringPresheaf 𝒪₂)}
    (f : (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap phi)).obj F ⟶
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap phi)).obj G) :
    (sheafifyThenRestrict J phi).obj F ⟶ (sheafifyThenRestrict J phi).obj G :=
  (restrictNatIso J phi).inv.app F ≫
    (moduleSheafification J 𝒪₁).map f ≫
    (restrictNatIso J phi).hom.app G

end ModuleSheafification

end PresheafOfModules
