/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of Finite Locally Free Module Sheaves

The finite-local-freeness predicate is owned for module sheaves over an arbitrary sheaf of rings.
This file contains its reusable restriction API on slice sites.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules.IsFiniteLocallyFree

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Finite local freeness is preserved by restriction to a slice site. -/
@[stacks 03DN "restriction stability"]
instance over (M : SheafOfModules.{w} R) (U : C) [IsFiniteLocallyFree M]
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
    [∀ V : Over U,
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    IsFiniteLocallyFree (M.over U) := sorry

end SheafOfModules.IsFiniteLocallyFree
