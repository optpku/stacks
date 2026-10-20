/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally finite-free retracts on ringed spaces

This file specializes the ringed-site finite-free-retract predicate to modules on a ringed
space and owns its point-neighborhood view.  The bridge from finite local freeness is the
generic `SheafOfModules.RingedSite.FiniteFreeRetract.isLocal_of_isFiniteLocallyFree` instance,
which applies here without a second ringed-space declaration.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
/-- The ringed-site finite-free-retract predicate has the expected point-neighborhood form on
a ringed space. -/
@[stacks 0B8K "local finite-free retract"]
theorem RingedSite.FiniteFreeRetract.IsLocal.existsNeighborhood
    {M : RingedSpace.Modules X} (hM : RingedSite.FiniteFreeRetract.IsLocal M) (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
      Nonempty (Retract (M.over U) (SheafOfModules.free.{u} I)) := sorry

/-- An invertible module sheaf is a retract of a finite free module sheaf on a neighborhood of
every point. -/
@[stacks 0B8K "locally a finite-free retract"]
theorem RingedSite.FiniteFreeRetract.existsNeighborhood_of_isInvertible
    (M : RingedSpace.Modules X) [MonoidalCategory.isInvertibleObject M] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
      Nonempty (Retract (M.over U) (SheafOfModules.free.{u} I)) := sorry

end SheafOfModules
