/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertible and trivial module sheaves on ringed spaces

This file develops the definitions and basic API for invertible and trivial sheaves of
modules on a ringed space.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

/-- A module sheaf `ℒ` on a ringed space `X` is *trivial* if it is isomorphic to the structure
sheaf `𝒪_X` as an `𝒪_X`-module. -/
@[stacks 01CS "trivial module"]
abbrev IsTrivial (ℒ : RingedSpace.Modules X) : Prop :=
  MonoidalCategory.isUnitObject ℒ

/-- The structure sheaf is trivial as an `𝒪_X`-module. -/
theorem unit_isTrivial :
    IsTrivial (X := X)
      (SheafOfModules.unit (RingedSpace.ringCatSheaf X) : RingedSpace.Modules X) := sorry

end AlgebraicGeometry.RingedSpace
