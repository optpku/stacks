/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-projective module sheaves and global sections

Global sections identify retracts of finite free module sheaves with finite-projective modules
over the global-sections ring.  The restricted functor is concrete; its landing proof and
equivalence are kept as separate propositions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite.Hom

variable (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [X.siteTopology.HasSheafCompose
  (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- Global sections of a retract of a finite free module sheaf form a finite-projective module
over `globalSectionsRing X`. -/
@[stacks 0FPX "finite-projective landing property"]
theorem moduleGlobalSections_mem_finiteProjective
    {F : ModuleCat.{w} X}
    (hF : SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf F) :
    ModuleCat.finiteProjective (globalSectionsRing X)
      ((moduleGlobalSectionsFunctor X).obj F) := sorry

/-- Global sections restricted from finite-free retracts to finite-projective modules over the
global-sections ring. -/
@[stacks 0FPX "restricted global-sections functor"]
noncomputable def finiteFreeRetractGlobalSections :
    (SheafOfModules.finiteFreeRetractModuleProperty
      X.structureSheaf).FullSubcategory ⥤
      ModuleCat.FiniteProjective (globalSectionsRing X) :=
  ObjectProperty.lift (ModuleCat.finiteProjective (globalSectionsRing X))
    ((SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf).ι ⋙
      moduleGlobalSectionsFunctor X)
    (fun F ↦ moduleGlobalSections_mem_finiteProjective X F.property)

/-- Lemma 21.49.1 (0FPX): the restricted global-sections functor is an equivalence from
finite-free-retract module sheaves to finite-projective modules over the global-sections ring. -/
@[stacks 0FPX]
theorem finiteFreeRetractGlobalSections_isEquivalence :
    Functor.IsEquivalence (finiteFreeRetractGlobalSections X) := sorry

end RingedSite.Hom
