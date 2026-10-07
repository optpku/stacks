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

end Sheafification

end SheafOfModules.RingedSite.KernelIdeal.IsSquareZero
