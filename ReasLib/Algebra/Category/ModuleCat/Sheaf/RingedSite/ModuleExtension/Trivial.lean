/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt.Splitting
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ModuleExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.TrivSqZeroExt (splittingHomSnd)

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Restriction of scalars along a trivialization followed by restriction along π recovers the
original 𝒪-module, via σ ≫ π = 𝟙 𝒪. -/
noncomputable def restrictEndpointIso (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (restrictionAlong σ).obj ((restrictionAlong π).obj M) ≅ M :=
  (restrictionAlongCompIso σ π).symm.app M ≪≫
    (eqToIso (congrArg (fun t ↦ (restrictionAlong t).obj M) hσ)) ≪≫
    (SheafOfModules.Restriction.idComponentIso'
      (ringSheafMap (𝟙 𝒪))
      ((sheafCompose J
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map_id 𝒪)
      M).symm

/-- Restriction of the kernel ideal along a trivialization recovers the descended kernel
module `ideal π`. -/
noncomputable def restrictIdealIso (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π) :
    KernelIdeal.restrict π σ ≅ ideal π :=
  (restrictionAlong σ).mapIso (restrictIdealModuleIso hπ.isSquareZero).symm ≪≫
    restrictEndpointIso π σ hσ (ideal π)

/-- The comparison `restrictIdealIso` is the composite of restriction of `restrictIdealModuleIso`
with the endpoint identification along σ ≫ π = 𝟙 𝒪. -/
theorem restrictIdealIso_spec (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π) :
    restrictIdealIso π σ hσ =
      (restrictionAlong σ).mapIso (restrictIdealModuleIso hπ.isSquareZero).symm ≪≫
        restrictEndpointIso π σ hσ (ideal π) := sorry

namespace ModuleExtension

/-- The restricted biproduct 𝒦 ⊞ ℱ, as an undeformed 𝒪'-module via π.  Source notation
ℱ ⊕ 𝒦 is this split-extension order 0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0. -/
noncomputable abbrev biprodRestrict (π : 𝒪' ⟶ 𝒪)
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪' :=
  (restrictionAlong π).obj K ⊞ (restrictionAlong π).obj F

/-- The left inclusion of the restricted biproduct. -/
noncomputable abbrev biprodInl (π : 𝒪' ⟶ 𝒪)
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (restrictionAlong π).obj K ⟶ biprodRestrict π F K :=
  biprod.inl

/-- The right projection of the restricted biproduct. -/
noncomputable abbrev biprodSnd (π : 𝒪' ⟶ 𝒪)
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    biprodRestrict π F K ⟶ (restrictionAlong π).obj F :=
  biprod.snd

/-- The ℐ-coordinate of a section of 𝒪' as a section of the descended kernel module. -/
noncomputable def splittingIdealSection (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π) (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪').obj.obj U) :
    (ideal π).val.obj U :=
  ((restrictIdealIso π σ hσ).hom.val.app U).hom (splittingHomSnd π σ hσ U r)

/-- The 𝒦-valued infinitesimal correction c(i ⊗ snd m) associated to a section of 𝒪'. -/
noncomputable def correction (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪').obj.obj U)
    (m : (biprodRestrict π F K).val.obj U) :
    ((restrictionAlong π).obj K).val.obj U :=
  (c.val.app U).hom
    (tensorSection 𝒪 U (splittingIdealSection π σ hσ U r)
      (((biprodSnd π F K).val.app U).hom m))

/-- Objectwise 𝒪'-action on 𝒦 ⊞ ℱ: the restriction-of-scalars π-action, plus the
inclusion of the infinitesimal correction along the splitting. -/
noncomputable def trivialSMul (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪').obj.obj U)
    (m : (biprodRestrict π F K).val.obj U) :
    (biprodRestrict π F K).val.obj U :=
  r • m + ((biprodInl π F K).val.app U).hom (correction π σ hσ c U r m)

/-- The objectwise 𝒪'-action is the π-action plus the included infinitesimal correction. -/
theorem trivialSMul_spec (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) (U : Cᵒᵖ)
    (r : (ringSheaf J 𝒪').obj.obj U)
    (m : (biprodRestrict π F K).val.obj U) :
    trivialSMul π σ hσ c U r m =
      r • m + ((biprodInl π F K).val.app U).hom (correction π σ hσ c U r m) := sorry

/-- The deformed scalar action satisfies the one smul law. -/
theorem trivialSMul_one_smul (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    (U : Cᵒᵖ) (m : (biprodRestrict π F K).val.obj U) :
    trivialSMul π σ hσ c U 1 m = m := sorry

/-- The deformed scalar action satisfies the mul smul law. -/
theorem trivialSMul_mul_smul (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    (U : Cᵒᵖ) (a b : (ringSheaf J 𝒪').obj.obj U) (m : (biprodRestrict π F K).val.obj U) :
    trivialSMul π σ hσ c U (a * b) m = trivialSMul π σ hσ c U a (trivialSMul π σ hσ c U b m) := sorry

/-- The deformed scalar action satisfies the smul zero law. -/
theorem trivialSMul_smul_zero (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    (U : Cᵒᵖ) (a : (ringSheaf J 𝒪').obj.obj U) :
    trivialSMul π σ hσ c U a 0 = 0 := sorry

/-- The deformed scalar action satisfies the smul add law. -/
theorem trivialSMul_smul_add (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    (U : Cᵒᵖ) (a : (ringSheaf J 𝒪').obj.obj U) (m n : (biprodRestrict π F K).val.obj U) :
    trivialSMul π σ hσ c U a (m + n) = trivialSMul π σ hσ c U a m + trivialSMul π σ hσ c U a n := sorry

/-- The deformed scalar action satisfies the add smul law. -/
theorem trivialSMul_add_smul (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    (U : Cᵒᵖ) (a b : (ringSheaf J 𝒪').obj.obj U) (m : (biprodRestrict π F K).val.obj U) :
    trivialSMul π σ hσ c U (a + b) m = trivialSMul π σ hσ c U a m + trivialSMul π σ hσ c U b m := sorry

/-- The deformed scalar action satisfies the zero smul law. -/
theorem trivialSMul_zero_smul (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    (U : Cᵒᵖ) (m : (biprodRestrict π F K).val.obj U) :
    trivialSMul π σ hσ c U 0 m = 0 := sorry

/-- The local 𝒪'-module structure on sections of 𝒦 ⊞ ℱ with the deformed action. -/
@[reducible] noncomputable def trivialSectionModule (π : 𝒪' ⟶ 𝒪)
    [IsFirstOrderThickening π] (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) (U : Cᵒᵖ) :
    Module ((ringSheaf J 𝒪').obj.obj U)
      ((biprodRestrict π F K).val.presheaf.obj U) where
  smul := trivialSMul π σ hσ c U
  one_smul := trivialSMul_one_smul π σ hσ c U
  mul_smul := trivialSMul_mul_smul π σ hσ c U
  smul_zero := trivialSMul_smul_zero π σ hσ c U
  smul_add := trivialSMul_smul_add π σ hσ c U
  add_smul := trivialSMul_add_smul π σ hσ c U
  zero_smul := trivialSMul_zero_smul π σ hσ c U

/-- Restriction of sections commutes with the deformed scalar action. -/
theorem trivialSMul_restrict (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    {U V : Cᵒᵖ} (f : U ⟶ V) (r : (ringSheaf J 𝒪').obj.obj U)
    (m : (biprodRestrict π F K).val.obj U) :
    (biprodRestrict π F K).val.presheaf.map f (trivialSMul π σ hσ c U r m) =
      trivialSMul π σ hσ c V ((ringSheaf J 𝒪').obj.map f r)
        ((biprodRestrict π F K).val.presheaf.map f m) := sorry

/-- The middle 𝒪'-module of the trivial extension: the additive sheaf of 𝒦 ⊞ ℱ
with the deformed splitting action. -/
noncomputable def trivialModule (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪' where
  val :=
    @PresheafOfModules.ofPresheaf C _ (ringSheaf J 𝒪').obj
      (biprodRestrict π F K).val.presheaf
      (fun X ↦ trivialSectionModule π σ hσ c X)
      (fun {_ _} f r m ↦ trivialSMul_restrict π σ hσ c f r m)
  isSheaf :=
    (congrArg (Presheaf.IsSheaf J)
      (@PresheafOfModules.ofPresheaf_presheaf C _ (ringSheaf J 𝒪').obj
        (biprodRestrict π F K).val.presheaf
        (fun X ↦ trivialSectionModule π σ hσ c X)
        (fun {_ _} f r m ↦ trivialSMul_restrict π σ hσ c f r m))).mpr
      (biprodRestrict π F K).isSheaf

/-- Forgetting the deformed 𝒪'-action recovers the additive sheaf of the restricted
biproduct 𝒦 ⊞ ℱ. -/
theorem toSheaf_trivialModule (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪')).obj (trivialModule π σ hσ c) =
      (SheafOfModules.toSheaf (ringSheaf J 𝒪')).obj (biprodRestrict π F K) := sorry

/-- The biproduct inclusion map is linear for the deformed action. -/
theorem trivialIncl_smul (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    (U : Cᵒᵖ) (r : (ringSheaf J 𝒪').obj.obj U) (m : ((restrictionAlong π).obj K).val.obj U) :
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (biprodInl π F K)).hom.app U
        ((((restrictionAlong π).obj K).val.obj U).isModule.smul r m) =
      trivialSMul π σ hσ c U r
        (((SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (biprodInl π F K)).hom.app U m) := sorry

/-- The inclusion 𝒦 ⟶ ℱ'_{c,triv} is the left biproduct inclusion, as an 𝒪'-linear map. -/
noncomputable def trivialIncl (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    (restrictionAlong π).obj K ⟶ trivialModule π σ hσ c where
  val :=
    PresheafOfModules.homMk
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (biprodInl π F K)).hom
      (trivialIncl_smul π σ hσ c)

/-- The biproduct projection map is linear for the deformed action. -/
theorem trivialProj_smul (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K)
    (U : Cᵒᵖ) (r : (ringSheaf J 𝒪').obj.obj U) (m : (trivialModule π σ hσ c).val.obj U) :
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (biprodSnd π F K)).hom.app U
        (trivialSMul π σ hσ c U r m) =
      (((restrictionAlong π).obj F).val.obj U).isModule.smul r
        (((SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (biprodSnd π F K)).hom.app U m) := sorry

/-- The projection ℱ'_{c,triv} ⟶ ℱ is the right biproduct projection, as an 𝒪'-linear map. -/
noncomputable def trivialProj (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    trivialModule π σ hσ c ⟶ (restrictionAlong π).obj F where
  val :=
    PresheafOfModules.homMk
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (biprodSnd π F K)).hom
      (trivialProj_smul π σ hσ c)

/-- The inclusion of the trivial extension forgets to the left biproduct inclusion. -/
theorem trivialIncl_toSheaf (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (trivialIncl π σ hσ c) =
      (SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (biprodInl π F K) := sorry

/-- The projection of the trivial extension forgets to the right biproduct projection. -/
theorem trivialProj_toSheaf (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (trivialProj π σ hσ c) =
      (SheafOfModules.toSheaf (ringSheaf J 𝒪')).map (biprodSnd π F K) := sorry

/-- The inclusion and projection of the trivial extension compose to zero. -/
theorem trivialExtension_zero (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    trivialIncl π σ hσ c ≫ trivialProj π σ hσ c = 0 := sorry

/-- The actual maps of the trivial extension form a short exact sequence. -/
theorem trivialExtension_shortExact (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    (ShortComplex.mk (trivialIncl π σ hσ c) (trivialProj π σ hσ c)
      (trivialExtension_zero π σ hσ c)).ShortExact := sorry

/-- The deformed splitting action induces the prescribed infinitesimal map. -/
theorem trivialExtension_compatible (π : 𝒪' ⟶ 𝒪) [IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    CompatibleC (IsFirstOrderThickening.isSquareZero (π := π))
      (trivialIncl π σ hσ c) (trivialProj π σ hσ c) c := sorry

/-- The trivial extension of ℱ by 𝒦 corresponding to c and the trivialization σ. -/
noncomputable def trivialExtension (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    ModuleExtension hπ.isSquareZero F K c :=
  of (trivialModule π σ hσ c) (trivialIncl π σ hσ c) (trivialProj π σ hσ c)
    (trivialExtension_zero π σ hσ c) (trivialExtension_shortExact π σ hσ c)
    (trivialExtension_compatible π σ hσ c)

/-- The middle 𝒪'-module of the trivial extension is `trivialModule`. -/
theorem trivialExtension_module (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    (trivialExtension π σ hσ c).module = trivialModule π σ hσ c := sorry

/-- The inclusion of the trivial extension is `trivialIncl`. -/
theorem trivialExtension_incl (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    (trivialExtension π σ hσ c).incl = trivialIncl π σ hσ c := sorry

/-- The projection of the trivial extension is `trivialProj`. -/
theorem trivialExtension_proj (π : 𝒪' ⟶ 𝒪) [hπ : IsFirstOrderThickening π]
    (σ : 𝒪 ⟶ 𝒪') (hσ : IsTrivialization σ π)
    {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (c : moduleTensor (ideal π) F ⟶ K) :
    (trivialExtension π σ hσ c).proj = trivialProj π σ hσ c := sorry

end ModuleExtension

end SheafOfModules.RingedSite.FirstOrderThickening
