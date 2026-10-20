/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Duality of locally finite-free retracts

The categorical comparison is owned by
`CategoryTheory.MonoidalClosed.tensorIhomUnitToEnd`.  This leaf contains only the geometric
criterion specific to module sheaves on a commutative ringed site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

section

variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

/-- A locally finite-free retract has invertible canonical tensor-to-endomorphism
comparison. -/
@[stacks 0FNY "local finite-free retract criterion", instance]
theorem FiniteFreeRetract.IsLocal.isIso_tensorIhomUnitToEnd
    (M : ringedSiteModuleCategory J 𝒪)
    [FiniteFreeRetract.IsLocal M] :
    IsIso (CategoryTheory.MonoidalClosed.tensorIhomUnitToEnd M) := sorry

/-- A locally finite-free retract is right-dualizable in the monoidal category of module
sheaves. -/
@[stacks 0FNZ "(2), right-dualizable"]
theorem FiniteFreeRetract.IsLocal.isRightDualizable
    (M : ringedSiteModuleCategory J 𝒪)
    [FiniteFreeRetract.IsLocal M] :
    IsRightDualizable M := sorry

end

section

/-- A dualizable module sheaf on a ringed site is locally a retract of a finite free module
sheaf. -/
@[stacks 0FNZ "(1)"]
theorem FiniteFreeRetract.IsLocal.ofExactPairing
    (M G : ringedSiteModuleCategory J 𝒪) [ExactPairing G M] :
    FiniteFreeRetract.IsLocal M := sorry

end

end SheafOfModules.RingedSite
