/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Quotient
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0B8S

# The kernel of a square-zero extension as a quotient module

For a square-zero morphism `π : A ⟶ Q`, the kernel ideal is annihilated by itself.  It therefore
descends canonically to a module over the quotient sheaf `A / ker π`.  This construction does not
choose a section of `π`; transporting it further to a `Q`-module belongs after the separate
first-isomorphism comparison `A / ker π ≅ Q`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.KernelIdeal.IsSquareZero

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {A Q : Sheaf J CommRingCat.{w}} {π : A ⟶ Q}

/-- A square-zero kernel ideal annihilates its underlying module sheaf. -/
@[stacks 04BP "square-zero kernel annihilates itself",
  stacks 0B8S "square-zero kernel-module descent"]
theorem isAnnihilated (hπ : KernelIdeal.IsSquareZero π) :
    IdealSheaf.IsAnnihilated (KernelIdeal.subobject π) (KernelIdeal.sheaf π) := sorry

section Sheafification

variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The kernel ideal of a square-zero extension, canonically descended to a module over
`A / ker π`. -/
@[stacks 04BP "square-zero quotient module",
  stacks 0B8S "coefficient module of a square-zero boundary"]
noncomputable abbrev quotientModule (hπ : KernelIdeal.IsSquareZero π) :
    SheafOfModules
      (ringSheaf J (IdealSheaf.Quotient.sheaf (KernelIdeal.subobject π))) :=
  IdealSheaf.Quotient.descend (KernelIdeal.subobject π) (KernelIdeal.sheaf π)
    hπ.isAnnihilated

/-- Forgetting the quotient action on `quotientModule hπ` recovers the underlying additive sheaf
of the kernel ideal. -/
@[stacks 04BP "underlying sheaf of the square-zero quotient module",
  stacks 0B8S "underlying coefficient sheaf of a square-zero boundary"]
noncomputable abbrev quotientModuleForgetIso (hπ : KernelIdeal.IsSquareZero π) :
    (SheafOfModules.toSheaf
      (ringSheaf J (IdealSheaf.Quotient.sheaf (KernelIdeal.subobject π)))).obj
        hπ.quotientModule ≅
      (SheafOfModules.toSheaf (ringSheaf J A)).obj (KernelIdeal.sheaf π) :=
  IdealSheaf.Quotient.forgetIso (KernelIdeal.subobject π) (KernelIdeal.sheaf π)
    hπ.isAnnihilated

/-- Under `quotientModuleForgetIso hπ`, the canonical image of a kernel section is the original
section. -/
@[stacks 04BP "underlying square-zero quotient-module unit",
  stacks 0B8S "underlying square-zero boundary coefficient"]
theorem quotientModuleForgetIso_unit (hπ : KernelIdeal.IsSquareZero π)
    (U : Cᵒᵖ) (m : (KernelIdeal.sheaf π).val.obj U) :
    hπ.quotientModuleForgetIso.hom.hom.app U
        (IdealSheaf.Quotient.unitApp (KernelIdeal.subobject π) (KernelIdeal.sheaf π)
          hπ.isAnnihilated U m) =
      m := sorry

/-- Pulling the action on `quotientModule hπ` back along the quotient projection recovers the
original `A`-action on the kernel ideal. -/
@[stacks 04BP "square-zero quotient-module scalar specification",
  stacks 0B8S "square-zero boundary coefficient scalar specification"]
theorem quotientModule_smul_projection (hπ : KernelIdeal.IsSquareZero π)
    (U : Cᵒᵖ) (r : A.obj.obj U) (m : (KernelIdeal.sheaf π).val.obj U) :
    hπ.quotientModuleForgetIso.hom.hom.app U
        ((CategoryTheory.toSheafify J
            (IdealSheaf.Quotient.presheaf (KernelIdeal.subobject π))).app U
              (IdealSheaf.Quotient.sectionProjection (KernelIdeal.subobject π) U r) •
          IdealSheaf.Quotient.unitApp (KernelIdeal.subobject π) (KernelIdeal.sheaf π)
            hπ.isAnnihilated U m) =
      r • m := sorry

/-- Transport the descended kernel module from `A / ker π` to a `Q`-module along an explicit
first-isomorphism certificate for `π`. -/
@[stacks 0B8S "square-zero kernel module over the target ring sheaf"]
noncomputable abbrev targetModule (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) :
    SheafOfModules (ringSheaf J Q) :=
  (SheafOfModules.restrictScalars (KernelIdeal.quotientRingIso π h).inv).obj
    hπ.quotientModule

/-- The underlying additive sheaf of `targetModule` is the kernel ideal sheaf. -/
@[stacks 0B8S "underlying target coefficient sheaf"]
noncomputable def targetModuleForgetIso (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) :
    (SheafOfModules.toSheaf (ringSheaf J Q)).obj (targetModule hπ h) ≅
    (SheafOfModules.toSheaf (ringSheaf J A)).obj (KernelIdeal.sheaf π) :=
  (SheafOfModules.restrictScalarsCompToSheaf
      (KernelIdeal.quotientRingIso π h).inv).app hπ.quotientModule ≪≫
    hπ.quotientModuleForgetIso

/-- The target scalar action is restriction of the quotient action along the supplied inverse.
The module objects specify the actual stored actions without introducing competing instances. -/
theorem targetModule_smul (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) (U : Cᵒᵖ)
    (q : Q.obj.obj U) (m : hπ.quotientModule.val.obj U) :
    ((targetModule hπ h).val.obj U).isModule.smul q m =
      (hπ.quotientModule.val.obj U).isModule.smul
        ((KernelIdeal.quotientRingIso π h).inv.hom.app U q) m := rfl

/-- For a locally surjective presentation, the target scalar action uses the specified local
quotient lift and sheaf amalgamation. -/
theorem targetModule_smul_localInverse [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) (h : IsIso (KernelIdeal.quotientComparison π))
    (U : Cᵒᵖ) (q : Q.obj.obj U) (m : hπ.quotientModule.val.obj U) :
    ((targetModule hπ h).val.obj U).isModule.smul q m =
      (hπ.quotientModule.val.obj U).isModule.smul (KernelIdeal.quotientInverseSection π U q) m := sorry

/-- A target scalar lifted from an `A`-section acts on the kernel by the original `A`-action.
This characterizes the source-facing descended action independently of any local lifts. -/
@[stacks 0B8S "target kernel-module scalar specification"]
theorem targetModule_smul_projection (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) (U : Cᵒᵖ)
    (r : A.obj.obj U) (m : (KernelIdeal.sheaf π).val.obj U) :
    (targetModuleForgetIso hπ h).hom.hom.app U
        (((targetModule hπ h).val.obj U).isModule.smul (π.hom.app U r)
          ((targetModuleForgetIso hπ h).inv.hom.app U m)) = r • m := sorry

/-- The additive target comparison is linear for the original source action. -/
theorem targetModuleRestrictHom_smul (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) (U : Cᵒᵖ)
    (r : A.obj.obj U) (m : ((restrictionAlong π).obj (targetModule hπ h)).val.obj U) :
    (targetModuleForgetIso hπ h).hom.hom.app U
        ((((restrictionAlong π).obj (targetModule hπ h)).val.obj U).isModule.smul r m) =
      ((KernelIdeal.sheaf π).val.obj U).isModule.smul r
        ((targetModuleForgetIso hπ h).hom.hom.app U m) := by
  have hi : (targetModuleForgetIso hπ h).inv.hom.app U
      ((targetModuleForgetIso hπ h).hom.hom.app U m) = m :=
    congrArg (fun f ↦ f.hom.app U m) (targetModuleForgetIso hπ h).hom_inv_id
  change (targetModuleForgetIso hπ h).hom.hom.app U
      (((targetModule hπ h).val.obj U).isModule.smul (π.hom.app U r) m) = _
  have hs := targetModule_smul_projection hπ h U r
    ((targetModuleForgetIso hπ h).hom.hom.app U m)
  rw [hi] at hs
  exact hs

/-- The inverse additive target comparison is linear for the original source action. -/
theorem targetModuleRestrictInv_smul (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) (U : Cᵒᵖ)
    (r : A.obj.obj U) (m : (KernelIdeal.sheaf π).val.obj U) :
    (targetModuleForgetIso hπ h).inv.hom.app U
        (((KernelIdeal.sheaf π).val.obj U).isModule.smul r m) =
      (((restrictionAlong π).obj (targetModule hπ h)).val.obj U).isModule.smul r
        ((targetModuleForgetIso hπ h).inv.hom.app U m) := by
  have hi (x : (targetModule hπ h).val.obj U) :
      (targetModuleForgetIso hπ h).inv.hom.app U
        ((targetModuleForgetIso hπ h).hom.hom.app U x) = x :=
    congrArg (fun f ↦ f.hom.app U x) (targetModuleForgetIso hπ h).hom_inv_id
  have hs := congrArg ((targetModuleForgetIso hπ h).inv.hom.app U)
    (targetModule_smul_projection hπ h U r m)
  change (targetModuleForgetIso hπ h).inv.hom.app U
      (((KernelIdeal.sheaf π).val.obj U).isModule.smul r m) =
    ((targetModule hπ h).val.obj U).isModule.smul (π.hom.app U r)
      ((targetModuleForgetIso hπ h).inv.hom.app U m)
  rw [hi] at hs
  exact hs.symm

/-- Restricting the descended target module recovers the original kernel module. Both maps are
exactly those of `targetModuleForgetIso`; linearity uses the source scalar projection formula. -/
@[stacks 0B8S "source-linear restriction of the descended square-zero kernel"]
noncomputable def targetModuleRestrictIso (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) :
    (restrictionAlong π).obj (targetModule hπ h) ≅ KernelIdeal.sheaf π where
  hom := ⟨PresheafOfModules.homMk (targetModuleForgetIso hπ h).hom.hom
    (targetModuleRestrictHom_smul hπ h)⟩
  inv := ⟨PresheafOfModules.homMk (targetModuleForgetIso hπ h).inv.hom
    (targetModuleRestrictInv_smul hπ h)⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    ext U m
    exact congrArg (fun f ↦ f.hom.app U m) (targetModuleForgetIso hπ h).hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    ext U m
    exact congrArg (fun f ↦ f.hom.app U m) (targetModuleForgetIso hπ h).inv_hom_id

/-- Forgetting the linear comparison gives precisely the original additive forward map. -/
@[simp]
theorem targetModuleRestrictIso_hom_toPresheaf (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) :
    ((SheafOfModules.toSheaf (ringSheaf J A)).map
      (targetModuleRestrictIso hπ h).hom).hom =
      (targetModuleForgetIso hπ h).hom.hom := rfl

/-- Forgetting the linear comparison gives precisely the original additive inverse map. -/
@[simp]
theorem targetModuleRestrictIso_inv_toPresheaf (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) :
    ((SheafOfModules.toSheaf (ringSheaf J A)).map
      (targetModuleRestrictIso hπ h).inv).hom =
      (targetModuleForgetIso hπ h).inv.hom := rfl

/-- The full additive comparison agrees with the existing forgetful isomorphism, after the
canonical identity comparison for restriction of scalars. -/
theorem targetModuleRestrictIso_toSheaf (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) :
    (SheafOfModules.toSheaf (ringSheaf J A)).mapIso (targetModuleRestrictIso hπ h) =
      (SheafOfModules.restrictScalarsCompToSheaf (ringSheafMap π)).app
        (targetModule hπ h) ≪≫ targetModuleForgetIso hπ h := by
  apply Iso.ext
  rfl

/-- The source-linear comparison retains the original projected-scalar formula. -/
theorem targetModuleRestrictIso_smul_projection (hπ : KernelIdeal.IsSquareZero π)
    (h : IsIso (KernelIdeal.quotientComparison π)) (U : Cᵒᵖ)
    (r : A.obj.obj U) (m : (KernelIdeal.sheaf π).val.obj U) :
    ((targetModuleRestrictIso hπ h).hom.val.app U).hom
      (r • ((targetModuleRestrictIso hπ h).inv.val.app U).hom m) = r • m :=
  targetModule_smul_projection hπ h U r m

end Sheafification

end SheafOfModules.RingedSite.KernelIdeal.IsSquareZero
