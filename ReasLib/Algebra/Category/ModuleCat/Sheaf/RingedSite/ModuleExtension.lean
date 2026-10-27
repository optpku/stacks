/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Infinitesimal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.Restriction

noncomputable section

universe u v

namespace SheafOfModules.RingedSite
namespace FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

section IdealModule

variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [Sheaf.IsLocallySurjective π]

/-- Restrict an 𝒪-linear infinitesimal map along π to a map of 𝒪'-modules. -/
noncomputable def restrictC {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    (hπ : KernelIdeal.IsSquareZero π) (c : moduleTensor (idealModule hπ) F ⟶ K) :
    moduleTensor (KernelIdeal.sheaf π) ((restrictionAlong π).obj F) ⟶
      (restrictionAlong π).obj K :=
  moduleTensorMap (restrictIdealModuleIso hπ).inv (𝟙 ((restrictionAlong π).obj F)) ≫
    Restriction.tensorComparison π (idealModule hπ) F ≫ (restrictionAlong π).map c

/-- The infinitesimal action of the square-zero kernel on lifts of sections of ℱ recovers
the prescribed 𝒪-linear map c. -/
def CompatibleC {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {E : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪'}
    (hπ : KernelIdeal.IsSquareZero π)
    (incl : (restrictionAlong π).obj K ⟶ E)
    (proj : E ⟶ (restrictionAlong π).obj F)
    (c : moduleTensor (idealModule hπ) F ⟶ K) : Prop :=
  ∀ (U : Cᵒᵖ) (f : (KernelIdeal.sheaf π).val.obj U) (s' : E.val.obj U),
    (incl.val.app U).hom
        ((restrictC hπ c).val.app U
          (tensorSection 𝒪' U f ((proj.val.app U).hom s'))) =
      KernelIdeal.ιApp π U f • s'

/-- An extension of an 𝒪-module ℱ by an 𝒪-module 𝒦 as an 𝒪'-module, with prescribed
infinitesimal map c : ℐ ⊗ ℱ ⟶ 𝒦. -/
structure ModuleExtension (hπ : KernelIdeal.IsSquareZero π)
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (idealModule hπ) F ⟶ K) where
  /-- The middle 𝒪'-module ℱ'. -/
  module : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪'
  /-- The inclusion 𝒦 ⟶ ℱ' after restriction of scalars along π. -/
  incl : (restrictionAlong π).obj K ⟶ module
  /-- The projection ℱ' ⟶ ℱ after restriction of scalars along π. -/
  proj : module ⟶ (restrictionAlong π).obj F
  /-- The two maps compose to zero. -/
  zero : incl ≫ proj = 0
  /-- The sequence 𝒦 ⟶ ℱ' ⟶ ℱ is short exact in Mod 𝒪'. -/
  shortExact : (ShortComplex.mk incl proj zero).ShortExact
  /-- The infinitesimal map of the sequence equals the prescribed c. -/
  compatible : CompatibleC hπ incl proj c

namespace ModuleExtension

variable {hπ : KernelIdeal.IsSquareZero π}
variable {F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
variable {c : moduleTensor (idealModule hπ) F ⟶ K}

/-- Assemble a prescribed extension from its middle module, endpoint maps, and defining certificates. -/
noncomputable def of (E : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
    (incl : (restrictionAlong π).obj K ⟶ E)
    (proj : E ⟶ (restrictionAlong π).obj F)
    (zero : incl ≫ proj = 0)
    (shortExact : (ShortComplex.mk incl proj zero).ShortExact)
    (compatible : CompatibleC hπ incl proj c) : ModuleExtension hπ F K c where
  module := E
  incl := incl
  proj := proj
  zero := zero
  shortExact := shortExact
  compatible := compatible

/-- The short complex 𝒦 ⟶ ℱ' ⟶ ℱ in Mod 𝒪' associated to an extension. -/
abbrev toShortComplex (E : ModuleExtension hπ F K c) :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :=
  ShortComplex.mk E.incl E.proj E.zero

/-- View an extension with prescribed c as a mixed-scalar `Extension`. -/
def toExtension (E : ModuleExtension hπ F K c) : Extension π :=
  ofMaps π K E.module F E.incl E.proj E.zero E.shortExact

/-- The canonical infinitesimal map of an extension recovers the prescribed c. -/
theorem infMap_eq (E : ModuleExtension hπ F K c) :
    infMap hπ E.toExtension = c := sorry

/-- Compatibility of the prescribed c is equality with the infinitesimal map. -/
theorem compatibleC_iff_infMap (E : ModuleExtension hπ F K c) :
    CompatibleC hπ E.incl E.proj c ↔ infMap hπ E.toExtension = c := sorry

/-- An extension is a short exact mixed-scalar sequence whose infinitesimal action
recovers the prescribed c. -/
theorem spec (E : ModuleExtension hπ F K c) :
    (toShortComplex E).ShortExact ∧ CompatibleC hπ E.incl E.proj c := sorry

/-- The restricted infinitesimal map of an extension is `restrictC` of the prescribed c. -/
theorem restrictC_spec (E : ModuleExtension hπ F K c)
    (U : Cᵒᵖ) (f : (KernelIdeal.sheaf π).val.obj U) (s' : E.module.val.obj U) :
    (E.incl.val.app U).hom
        ((restrictC hπ c).val.app U
          (tensorSection 𝒪' U f ((E.proj.val.app U).hom s'))) =
      KernelIdeal.ιApp π U f • s' := sorry

end ModuleExtension

end IdealModule

end FirstOrderThickening
end SheafOfModules.RingedSite
