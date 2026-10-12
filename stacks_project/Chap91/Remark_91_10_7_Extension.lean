/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
public import stacks_project.Chap91.«91_10_0_1_Extension»

/-!
# 08MB extensions with prescribed infinitesimal maps

After identifying underlying topoi, a first-order thickening of ringed topoi is a same-site
morphism π : 𝒪' ⟶ 𝒪 with locally surjective square-zero kernel.  This leaf owns the induced
map of kernels along a morphism of thickenings, and the 08MB mixed-scalar extensions of an
𝒪-module ℱ by an 𝒪-module 𝒦 with a prescribed infinitesimal map c : ℐ ⊗ ℱ ⟶ 𝒦.  The kernel
ideal as an 𝒪-module is the existing 08MB `idealModule`.
-/

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

/-- Restriction of scalars along a composite morphism of commutative ring sheaves is
the composite of the corresponding restriction functors. -/
noncomputable def restrictionAlongCompIso {𝒪₁ 𝒪₂ 𝒪₃ : Sheaf J CommRingCat.{max u v}}
    (α : 𝒪₁ ⟶ 𝒪₂) (β : 𝒪₂ ⟶ 𝒪₃) :
    restrictionAlong (α ≫ β) ≅ restrictionAlong β ⋙ restrictionAlong α :=
  eqToIso (congrArg (fun t ↦ SheafOfModules.restrictScalars.{max u v} t)
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map_comp α β)) ≪≫
    (SheafOfModules.Restriction.compIso (ringSheafMap α) (ringSheafMap β)).symm

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

/-- An 08MB extension of an 𝒪-module ℱ by an 𝒪-module 𝒦 as an 𝒪'-module, with prescribed
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

/-- Assemble an 08MB extension from a middle 𝒪'-module and the two mixed-scalar maps. -/
noncomputable def of (E : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
    (incl : (restrictionAlong π).obj K ⟶ E)
    (proj : E ⟶ (restrictionAlong π).obj F) :
    ModuleExtension hπ F K c where
  module := E
  incl := incl
  proj := proj
  zero := sorry
  shortExact := sorry
  compatible := sorry

/-- The short complex 𝒦 ⟶ ℱ' ⟶ ℱ in Mod 𝒪' associated to an 08MB extension. -/
abbrev toShortComplex (E : ModuleExtension hπ F K c) :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') :=
  ShortComplex.mk E.incl E.proj E.zero

/-- View an 08MB extension with prescribed c as a mixed-scalar `Extension`. -/
def toExtension (E : ModuleExtension hπ F K c) : Extension π :=
  ofMaps π K E.module F E.incl E.proj E.zero E.shortExact

/-- The canonical infinitesimal map of an 08MB extension recovers the prescribed c. -/
theorem infMap_eq (E : ModuleExtension hπ F K c) :
    infMap hπ E.toExtension = c := sorry

/-- Compatibility of the prescribed c is equality with the 08MB infinitesimal map. -/
theorem CompatibleC_iff_infMap (E : ModuleExtension hπ F K c) :
    CompatibleC hπ E.incl E.proj c ↔ infMap hπ E.toExtension = c := sorry

/-- An 08MB extension is a short exact mixed-scalar sequence whose infinitesimal action
recovers the prescribed c. -/
theorem spec (E : ModuleExtension hπ F K c) :
    (toShortComplex E).ShortExact ∧ CompatibleC hπ E.incl E.proj c := sorry

/-- The restricted infinitesimal map of an 08MB extension is `restrictC` of the prescribed c. -/
theorem restrictC_spec (E : ModuleExtension hπ F K c)
    (U : Cᵒᵖ) (f : (KernelIdeal.sheaf π).val.obj U) (s' : E.module.val.obj U) :
    (E.incl.val.app U).hom
        ((restrictC hπ c).val.app U
          (tensorSection 𝒪' U f ((E.proj.val.app U).hom s'))) =
      KernelIdeal.ιApp π U f • s' := sorry

end ModuleExtension

end IdealModule

section IdealMap

variable {𝒪 𝒪1 𝒪2 : Sheaf J CommRingCat.{max u v}}
variable {π1 : 𝒪1 ⟶ 𝒪} {π2 : 𝒪2 ⟶ 𝒪}
variable [Sheaf.IsLocallySurjective π1] [Sheaf.IsLocallySurjective π2]

/-- The kernel-ideal inclusion remains a monomorphism after restriction of scalars. -/
instance instMono_restrictionAlong_kernelIdeal_ι (h : 𝒪2 ⟶ 𝒪1) :
    Mono ((restrictionAlong h).map (KernelIdeal.ι π1)) := sorry

/-- The 𝒪'₂-linear comparison of kernel ideals induced by a ring-sheaf map over 𝒪. -/
noncomputable def kernelIdealRestrictMap (h : 𝒪2 ⟶ 𝒪1) :
    KernelIdeal.sheaf (h ≫ π1) ⟶ (restrictionAlong h).obj (KernelIdeal.sheaf π1) :=
  Abelian.monoLift ((restrictionAlong h).map (KernelIdeal.ι π1))
    (KernelIdeal.ι (h ≫ π1) ≫
      SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap h))
    sorry

/-- The additive comparison ℐ₂ ⟶ ℐ₁ of kernel ideals induced by h : 𝒪'₂ ⟶ 𝒪'₁. -/
noncomputable def idealMap_toSheaf (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2) :
    (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj (idealModule hπ2) ⟶
      (SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj (idealModule hπ1) :=
  (hπ2.targetModuleForgetIso inferInstance).hom ≫
    KernelIdeal.additiveLift π1
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map (KernelIdeal.ι π2) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap h))
      sorry ≫
    (hπ1.targetModuleForgetIso inferInstance).inv

/-- h^♯ : 𝒪'₂ ⟶ 𝒪'₁ induces an 𝒪-module map ℐ₂ ⟶ ℐ₁ of square-zero kernel ideals. -/
noncomputable def idealMap (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2) :
    idealModule hπ2 ⟶ idealModule hπ1 where
  val := PresheafOfModules.homMk (idealMap_toSheaf h h_comm hπ1 hπ2).hom sorry

/-- The induced kernel map is compatible with the inclusions of ℐᵢ into 𝒪'ᵢ. -/
theorem idealMap_comp_ι (h : 𝒪2 ⟶ 𝒪1) (h_comm : h ≫ π1 = π2)
    (hπ1 : KernelIdeal.IsSquareZero π1) (hπ2 : KernelIdeal.IsSquareZero π2) :
    (hπ2.targetModuleForgetIso inferInstance).inv ≫
        (SheafOfModules.toSheaf (ringSheaf J 𝒪)).map (idealMap h h_comm hπ1 hπ2) ≫
          (hπ1.targetModuleForgetIso inferInstance).hom ≫
            (SheafOfModules.toSheaf (ringSheaf J 𝒪1)).map (KernelIdeal.ι π1) =
      (SheafOfModules.toSheaf (ringSheaf J 𝒪2)).map (KernelIdeal.ι π2) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap h) := sorry

end IdealMap

end FirstOrderThickening
end SheafOfModules.RingedSite
