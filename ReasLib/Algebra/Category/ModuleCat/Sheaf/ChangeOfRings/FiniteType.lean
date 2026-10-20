/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite type under restriction of scalars

This file separates the algebraic change-of-rings part of finite generation from any
topological pushforward. Restriction of scalars always reflects finite type; it preserves finite
type when the map of ring sheaves is locally surjective.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R R' : Sheaf J RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace IsFiniteType

/-- Finite type after restriction of scalars implies finite type over the larger sheaf of rings.
No surjectivity hypothesis is needed in this direction. -/
@[stacks 01C4 "restriction of scalars reflects finite type"]
theorem of_restrictScalars
    (α : R ⟶ R') (M : SheafOfModules.{w} R')
    (hM : ((SheafOfModules.restrictScalars.{w} α).obj M).IsFiniteType) :
    M.IsFiniteType := sorry

/-- Along a locally surjective map of ring sheaves, a module sheaf is of finite type exactly
when its restriction of scalars is. -/
@[stacks 01C4 "change of rings"]
theorem restrictScalars_iff
    (α : R ⟶ R') [Sheaf.IsLocallySurjective α]
    (M : SheafOfModules.{w} R') :
    ((SheafOfModules.restrictScalars.{w} α).obj M).IsFiniteType ↔ M.IsFiniteType := sorry

end IsFiniteType

/-- Restriction of scalars along a locally surjective map of ring sheaves preserves finite type. -/
@[stacks 01C4 "restriction of scalars preserves finite type"]
instance restrictScalars_isFiniteType
    (α : R ⟶ R') [Sheaf.IsLocallySurjective α]
    (M : SheafOfModules.{w} R') [M.IsFiniteType] :
    ((SheafOfModules.restrictScalars.{w} α).obj M).IsFiniteType := sorry

variable (α : R ⟶ R') [Sheaf.IsLocallySurjective α]
variable (M : SheafOfModules.{w} R') [M.IsFiniteType]

#synth ((SheafOfModules.restrictScalars.{w} α).obj M).IsFiniteType

end SheafOfModules
