/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul
import Mathlib.Tactic.CrossRefAttribute

/-!
# Endomorphisms of the structure module on a slice

Every endomorphism of the restricted structure module is multiplication by a unique local
section.  The inverse map is explicit: view the endomorphism as a section of the structure module
and evaluate that section at the terminal object of the slice.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w})

/-- Recover the local section defining an endomorphism of the restricted structure module. -/
@[stacks 03EM "local section from a structure-module endomorphism"]
noncomputable def sectionActionUnitInv (U : C)
    (f : End ((unitModule J O).over U)) : O.obj.obj (op U) :=
  sectionsOverEquiv (unitModule J O) U
    (((unitModule J O).over U).unitHomEquiv f)

/-- Recovering a section after forming its multiplication endomorphism gives the original
section. -/
@[simp]
theorem sectionActionUnitInv_action (U : C) (r : O.obj.obj (op U)) :
    sectionActionUnitInv O U (sectionAction O (unitModule J O) U r) = r := sorry

/-- Multiplication by the section recovered from a structure-module endomorphism gives the
original endomorphism. -/
@[simp]
theorem sectionAction_actionUnitInv (U : C) (f : End ((unitModule J O).over U)) :
    sectionAction O (unitModule J O) U (sectionActionUnitInv O U f) = f := sorry

/-- Local sections over `U` are canonically the endomorphism ring of the structure module
restricted to `C / U`. -/
@[stacks 03EM "local sections as structure-module endomorphisms"]
noncomputable def sectionActionUnitEquiv (U : C) :
    O.obj.obj (op U) ≃+* End ((unitModule J O).over U) :=
  { sectionAction O (unitModule J O) U with
    invFun := sectionActionUnitInv O U
    left_inv := sectionActionUnitInv_action O U
    right_inv := sectionAction_actionUnitInv O U }

/-- The structure-module endomorphism equivalence sends a section to its multiplication
endomorphism. -/
@[simp]
theorem sectionActionUnitEquiv_apply (U : C) (r : O.obj.obj (op U)) :
    sectionActionUnitEquiv O U r = sectionAction O (unitModule J O) U r := sorry

/-- The inverse structure-module endomorphism equivalence is terminal evaluation. -/
@[simp]
theorem sectionActionUnitEquiv_symm_apply
    (U : C) (f : End ((unitModule J O).over U)) :
    (sectionActionUnitEquiv O U).symm f = sectionActionUnitInv O U f := sorry

end SheafOfModules.RingedSite
