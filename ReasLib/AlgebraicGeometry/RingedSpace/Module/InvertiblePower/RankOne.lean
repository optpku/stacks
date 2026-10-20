/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Rank.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Rank one for integral tensor powers

Integral tensor powers of a rank-one module sheaf remain rank one.  The stalk theorem is stated
through the basis-free `ModuleCat.freeRankOne` property, so no local generator is selected.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.InvertiblePower

variable {X : RingedSpace.{u}}

/-- Every integral tensor power of a finite locally free rank-one module sheaf again has finite
local rank one. -/
@[stacks 01CU "rank one for integral tensor powers", stacks 0GTA "rank-one ideal powers", instance]
instance isFiniteLocallyFreeOfRankOne
    (L : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L] (n : ℤ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (L ^⊗ n) := sorry

/-- Every stalk of an integral tensor power of a rank-one module sheaf is free of rank one,
without a chosen generator. -/
@[stacks 0GTA "rank-one stalk of an integral tensor power"]
theorem stalk_freeRankOne
    (L : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank 1 L]
    (n : ℤ) (x : X) :
    ModuleCat.freeRankOne (X.presheaf.stalk x)
      (stalkModuleCat (L ^⊗ n) x) := sorry

end AlgebraicGeometry.RingedSpace.InvertiblePower
