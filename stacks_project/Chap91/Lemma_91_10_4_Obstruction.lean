/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FreeFlatCover
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import ReasLib.CategoryTheory.Abelian.Extension.PullPush
public import stacks_project.Chap91.Remark_91_10_10_Thickening
public import stacks_project.Chap91.Remark_91_10_7_Extension

/-!
# Existence obstruction for mixed-scalar extensions on a first-order thickening

On a same-site first-order thickening π : 𝒪' ⟶ 𝒪, an 𝒪-linear map
c : ℐ ⊗ ℱ ⟶ 𝒦 determines a canonical class in Ext ℱ 𝒦 2.  Vanishing of this class is
equivalent to existence of an 08MB sequence with infinitesimal map c.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace ModuleExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- The chosen functorial injective embedding of an 𝒪-module. -/
noncomputable abbrev injectiveι
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    K ⟶ HasFunctorialInjectives.obj K :=
  HasFunctorialInjectives.ι.app K

/-- The chosen functorial injective embedding is the component of the functorial
injective natural transformation. -/
theorem injectiveι_eq
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    injectiveι K = HasFunctorialInjectives.ι.app K := sorry

/-- The cokernel of the chosen functorial injective embedding of an 𝒪-module. -/
noncomputable abbrev injectiveCokernel
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪 :=
  cokernel (injectiveι K)

/-- The cokernel of the chosen embedding is the cokernel of `injectiveι`. -/
theorem injectiveCokernel_eq
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    injectiveCokernel K = cokernel (injectiveι K) := sorry

/-- The injective presentation sequence 0 ⟶ 𝒦 ⟶ 𝒦' ⟶ 𝒬 ⟶ 0. -/
noncomputable def injectiveCokernelSES
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    CategoryTheory.Extension K (injectiveCokernel K) where
  E := HasFunctorialInjectives.obj K
  f := injectiveι K
  g := cokernel.π (injectiveι K)
  zero := cokernel.condition _
  shortExact := sorry

/-- `injectiveCokernelSES` is the kernel-cokernel sequence of the chosen injective
embedding of 𝒦. -/
theorem injectiveCokernelSES_spec
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (injectiveCokernelSES K).E = HasFunctorialInjectives.obj K ∧
      (injectiveCokernelSES K).f = injectiveι K := sorry

/-- The quotient map of `injectiveCokernelSES` is the cokernel projection of the chosen
embedding. -/
theorem injectiveCokernelSES_g
    (K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (injectiveCokernelSES K).g = cokernel.π (injectiveι K) := sorry

variable (π : 𝒪' ⟶ 𝒪)
variable [hπ : IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J 𝒪')]

/-- The kernel sequence 0 ⟶ 𝒥 ⟶ ℋ' ⟶ ℱ ⟶ 0 of the canonical free flat 𝒪'-cover of ℱ. -/
noncomputable def flatCoverKernelExtension
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    CategoryTheory.Extension
      (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F)))
      ((restrictionAlong π).obj F) where
  E := FreeFlatCover.obj ((restrictionAlong π).obj F)
  f := kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))
  g := FreeFlatCover.πApp ((restrictionAlong π).obj F)
  zero := kernel.condition _
  shortExact := sorry

/-- The kernel sequence of the free flat cover has middle object the canonical free
flat 𝒪'-module. -/
theorem flatCoverKernelExtension_spec
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    (flatCoverKernelExtension π F).E =
        FreeFlatCover.obj ((restrictionAlong π).obj F) ∧
      (flatCoverKernelExtension π F).g =
        FreeFlatCover.πApp ((restrictionAlong π).obj F) := sorry

/-- The kernel-ideal action on the free flat cover is killed by the covering map. -/
theorem action_flatCover_comp_πApp
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    IdealSheaf.action (KernelIdeal.subobject π)
          (FreeFlatCover.obj ((restrictionAlong π).obj F)) ≫
        FreeFlatCover.πApp ((restrictionAlong π).obj F) = 0 := sorry

/-- The comparison ℐℋ' / ℐ𝒥 ⟶ 𝒥 / ℐ𝒥 of 𝒪'-modules. -/
noncomputable def idealQuotientIncl
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    cokernel
        ((tensorLeft (KernelIdeal.sheaf π)).map
          (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F)))) ⟶
      cokernel
        (IdealSheaf.action (KernelIdeal.subobject π)
          (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F)))) :=
  cokernel.desc
    ((tensorLeft (KernelIdeal.sheaf π)).map
      (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))))
    (kernel.lift (FreeFlatCover.πApp ((restrictionAlong π).obj F))
        (IdealSheaf.action (KernelIdeal.subobject π)
          (FreeFlatCover.obj ((restrictionAlong π).obj F)))
        (action_flatCover_comp_πApp π F) ≫
      cokernel.π
        (IdealSheaf.action (KernelIdeal.subobject π)
          (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F)))))
    sorry

/-- `idealQuotientIncl` is induced by the inclusion of ℐℋ' into 𝒥. -/
theorem idealQuotientIncl_spec
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    cokernel.π
          ((tensorLeft (KernelIdeal.sheaf π)).map
            (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F)))) ≫
        idealQuotientIncl π F =
      kernel.lift (FreeFlatCover.πApp ((restrictionAlong π).obj F))
          (IdealSheaf.action (KernelIdeal.subobject π)
            (FreeFlatCover.obj ((restrictionAlong π).obj F)))
          (action_flatCover_comp_πApp π F) ≫
        cokernel.π
          (IdealSheaf.action (KernelIdeal.subobject π)
            (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F)))) := sorry

/-- After extension of scalars along π, the comparison ℐℋ' / ℐ𝒥 ⟶ 𝒥 / ℐ𝒥 is a
monomorphism of 𝒪-modules. -/
instance idealQuotientIncl_extendScalars_mono
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) :
    Mono
      ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
        (idealQuotientIncl π F)) := sorry

/-- The tensor of the kernel inclusion is annihilated by ℐ ⊗ πApp composed with the
restricted infinitesimal map. -/
theorem idealQuotientToKernel_comp_zero
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    (tensorLeft (KernelIdeal.sheaf π)).map
          (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))) ≫
        ((tensorLeft (KernelIdeal.sheaf π)).map
            (FreeFlatCover.πApp ((restrictionAlong π).obj F)) ≫
          restrictC hπ.isSquareZero c) = 0 := sorry

/-- The comparison ℐℋ' / ℐ𝒥 ⟶ 𝒦 of 𝒪'-modules induced by c. -/
noncomputable def idealQuotientToKernel
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    cokernel
        ((tensorLeft (KernelIdeal.sheaf π)).map
          (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F)))) ⟶
      (restrictionAlong π).obj K :=
  cokernel.desc
    ((tensorLeft (KernelIdeal.sheaf π)).map
      (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F))))
    ((tensorLeft (KernelIdeal.sheaf π)).map
        (FreeFlatCover.πApp ((restrictionAlong π).obj F)) ≫
      restrictC hπ.isSquareZero c)
    (idealQuotientToKernel_comp_zero π F K c)

/-- `idealQuotientToKernel` is c after the tensor of the free flat covering map. -/
theorem idealQuotientToKernel_spec
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    cokernel.π
          ((tensorLeft (KernelIdeal.sheaf π)).map
            (kernel.ι (FreeFlatCover.πApp ((restrictionAlong π).obj F)))) ≫
        idealQuotientToKernel π F K c =
      (tensorLeft (KernelIdeal.sheaf π)).map
          (FreeFlatCover.πApp ((restrictionAlong π).obj F)) ≫
        restrictC hπ.isSquareZero c := sorry

/-- The 𝒪-linear extension of c along the chosen injective embedding of 𝒦. -/
noncomputable def cExtend
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    moduleTensor (ideal π) F ⟶ HasFunctorialInjectives.obj K :=
  c ≫ injectiveι K

/-- `cExtend` is postcomposition of c with the chosen injective embedding. -/
theorem cExtend_eq
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    cExtend π F K c = c ≫ injectiveι K := sorry

/-- The 𝒪-linear dotted lift 𝒥 / ℐ𝒥 ⟶ 𝒦 supplied by injectivity of 𝒦. -/
noncomputable def liftThroughInjective
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj
        (cokernel
          (IdealSheaf.action (KernelIdeal.subobject π)
            (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F))))) ⟶
      K :=
  @Injective.factorThru (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) _
      K _ _ ‹Injective K›
      ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
          (idealQuotientToKernel π F K c) ≫
        (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
            (ringSheafMap π)).counit.app K)
      ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
        (idealQuotientIncl π F))
      (idealQuotientIncl_extendScalars_mono π F)

/-- `liftThroughInjective` is the injective lift of the descended comparison
ℐℋ' / ℐ𝒥 ⟶ 𝒦 along ℐℋ' / ℐ𝒥 ⟶ 𝒥 / ℐ𝒥. -/
theorem liftThroughInjective_comp
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
          (idealQuotientIncl π F) ≫
        liftThroughInjective π F K c =
      (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
          (idealQuotientToKernel π F K c) ≫
        (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
            (ringSheafMap π)).counit.app K := sorry

/-- An 08MB extension of ℱ by an injective 𝒦 with infinitesimal map c, obtained by
pushing out the kernel sequence of a flat cover along the dotted lift supplied by
injectivity. -/
noncomputable def ofInjective
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    ModuleExtension hπ.isSquareZero F K c :=
  let γ' :=
    cokernel.π
        (IdealSheaf.action (KernelIdeal.subobject π)
          (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F)))) ≫
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
          (ringSheafMap π)).unit.app
        (cokernel
          (IdealSheaf.action (KernelIdeal.subobject π)
            (kernel (FreeFlatCover.πApp ((restrictionAlong π).obj F))))) ≫
      (restrictionAlong π).map (liftThroughInjective π F K c)
  let S := CategoryTheory.Extension.pushout γ' (flatCoverKernelExtension π F)
  of S.E S.f S.g

/-- The injective-case 08MB extension is short exact with infinitesimal map c. -/
theorem ofInjective_spec
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    (toShortComplex (ofInjective π F K c)).ShortExact ∧
      CompatibleC hπ.isSquareZero (ofInjective π F K c).incl
        (ofInjective π F K c).proj c := sorry

/-- The infinitesimal map of `ofInjective` equals the prescribed c. -/
theorem ofInjective_infMap
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    infMap hπ.isSquareZero (ofInjective π F K c).toExtension = c := sorry

/-- The 08MB envelope of ℱ by the chosen injective target, with infinitesimal map
c extended along the chosen embedding. -/
noncomputable def liftToInjective
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    ModuleExtension hπ.isSquareZero F (HasFunctorialInjectives.obj K)
      (cExtend π F K c) :=
  ofInjective π F (HasFunctorialInjectives.obj K) (cExtend π F K c)

/-- `liftToInjective` is the injective-case envelope of the extended infinitesimal map. -/
theorem liftToInjective_eq
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    liftToInjective π F K c =
      ofInjective π F (HasFunctorialInjectives.obj K) (cExtend π F K c) := sorry

/-- Same-thickening pushout of an 08MB extension along a map of kernel 𝒪-modules. -/
noncomputable def pushoutAlong
    {F K K' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K} (k : K ⟶ K')
    (E : ModuleExtension hπ.isSquareZero F K c) :
    ModuleExtension hπ.isSquareZero F K' (c ≫ k) :=
  let S :=
    CategoryTheory.Extension.pushout ((restrictionAlong π).map k)
      { E := E.module
        f := E.incl
        g := E.proj
        zero := E.zero
        shortExact := E.shortExact }
  of S.E S.f S.g

/-- The infinitesimal map of a same-thickening pushout is postcomposition with k. -/
theorem pushoutAlong_infMap
    {F K K' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪}
    {c : moduleTensor (ideal π) F ⟶ K} (k : K ⟶ K')
    (E : ModuleExtension hπ.isSquareZero F K c) :
    infMap hπ.isSquareZero (pushoutAlong π k E).toExtension = c ≫ k := sorry

/-- Pushout of the injective-case envelope along 𝒦' ⟶ 𝒬. -/
noncomputable def envelopePushout
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    ModuleExtension hπ.isSquareZero F (injectiveCokernel K)
      (cExtend π F K c ≫ cokernel.π (injectiveι K)) :=
  pushoutAlong π (cokernel.π (injectiveι K)) (liftToInjective π F K c)

/-- `envelopePushout` is the same-thickening pushout of `liftToInjective` along the
cokernel projection of the chosen embedding. -/
theorem envelopePushout_eq
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    envelopePushout π F K c =
      pushoutAlong π (cokernel.π (injectiveι K)) (liftToInjective π F K c) := sorry

/-- The descended 𝒪-module extension 0 ⟶ 𝒬 ⟶ 𝒟 ⟶ ℱ ⟶ 0 representing the Ext¹ form
of the existence obstruction. -/
noncomputable def descendedExtension
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    CategoryTheory.Extension (injectiveCokernel K) F where
  E :=
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj
      (envelopePushout π F K c).module
  f :=
    (SheafOfModules.restrictHomEquivOfIsLocallySurjective (ringSheafMap π)
        (injectiveCokernel K)
        ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj
          (envelopePushout π F K c).module)).symm
      ((envelopePushout π F K c).incl ≫
        (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
            (ringSheafMap π)).unit.app (envelopePushout π F K c).module)
  g :=
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
        (envelopePushout π F K c).proj ≫
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
          (ringSheafMap π)).counit.app F
  zero := sorry
  shortExact := sorry

/-- The left and right maps of `descendedExtension` are the extension-restriction
conjugates of the envelope pushout. -/
theorem descendedExtension_spec
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    (descendedExtension π F K c).E =
        (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj
          (envelopePushout π F K c).module ∧
      (descendedExtension π F K c).g =
        (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map
            (envelopePushout π F K c).proj ≫
          (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
              (ringSheafMap π)).counit.app F := sorry

variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)]

/-- The existence obstruction o(ℱ, 𝒦, c) ∈ Ext²_𝒪(ℱ, 𝒦). -/
noncomputable def obstruction
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) : Ext F K 2 :=
  (descendedExtension π F K c).extClass.comp
    (injectiveCokernelSES K).extClass (rfl : 1 + 1 = 2)

/-- `obstruction` is the Ext.comp of the descended quotient class with the
injective-presentation class. -/
theorem obstruction_spec
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)
    (c : moduleTensor (ideal π) F ⟶ K) :
    obstruction π F K c =
      (descendedExtension π F K c).extClass.comp
        (injectiveCokernelSES K).extClass (rfl : 1 + 1 = 2) := sorry

/-- The existence obstruction vanishes when 𝒦 is injective. -/
theorem obstruction_eq_zero_of_injective
    (F K : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪) [Injective K]
    (c : moduleTensor (ideal π) F ⟶ K) :
    obstruction π F K c = 0 := sorry

end ModuleExtension
end SheafOfModules.RingedSite.FirstOrderThickening
