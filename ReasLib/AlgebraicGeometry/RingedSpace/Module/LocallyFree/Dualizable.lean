/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Duality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dualizability of finite locally free modules on ringed spaces

Finite local freeness supplies the local finite-free retract criterion needed by the generic
duality API for module sheaves on a ringed site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.IsFiniteLocallyFree

variable {X : RingedSpace.{u}}

/-- A finite locally free module sheaf on a ringed space is right-dualizable. -/
@[stacks 0FNZ "(2), ringed-space finite locally free form"]
theorem isRightDualizable (E : X.Modules) [E.IsFiniteLocallyFree] :
    IsRightDualizable E := sorry

end SheafOfModules.IsFiniteLocallyFree
