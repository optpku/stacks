/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Localization
import StacksCheckRecall

/-!
# Lemma 24.19.2

The functorial localized DG projection formula is owned by
`ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Localization`.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.LeftDifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{w}) (U : C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable [(SheafOfModules.RingedSite.Localization.restriction O U :
  SheafOfModules.{w} (ringSheaf J O) ⥤
    SheafOfModules.{w} ((ringSheaf J O).over U)).LaxMonoidal]
variable [(SheafOfModules.RingedSite.Localization.restriction O U :
  SheafOfModules.{w} (ringSheaf J O) ⥤
    SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint]
variable (A : DGA(O))
variable (M : Mod((restrictedAlgebra O U A), d)) (N : LMod(A, d))

/- Lemma 24.19.2 (0FRX): localized DG extension by zero commutes naturally in both
module variables with tensoring against an ambient left DG module. -/
@[stacks 0FRX]
#check
  (ProjectionFormula.natIso O U A :
    ProjectionFormula.sourceFunctor O U A ≅
      ProjectionFormula.targetFunctor O U A)

-- The component of the functorial comparison is the textbook projection formula.
#check
  (ProjectionFormula.iso O U A M N :
    tensor ((lowerShriek O U A).obj M) N ≅
      (SheafOfModules.RingedSite.Localization.lowerShriekComplex O U).obj
        (tensor M ((restrictionLeft O U A).obj N)))

end SheafOfModules.RingedSite.DifferentialGradedModule.Localization

end
