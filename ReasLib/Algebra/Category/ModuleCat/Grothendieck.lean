/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.Algebra.Category.ModuleCat.AB

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe r w
namespace ModuleCat
variable (R : Type r) [Ring R]

/-- Filtered colimits of modules are exact, independently of the universe of the ring. -/
instance ab5OfUniverse : AB5 (ModuleCat.{w} R) := sorry

/-- Modules over a ring small in the carrier universe form a Grothendieck abelian category. -/
instance isGrothendieckAbelianOfSmall [Small.{w} R] :
    IsGrothendieckAbelian.{w} (ModuleCat.{w} R) where

end ModuleCat
