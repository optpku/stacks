/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact colimits of flat objects

Flatness is stable under a colimit when that colimit is exact and tensoring in the varying
factor preserves it.  This categorical owner is shared by graded modules, complexes, sheaves,
and later base-change-stable flatness properties.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v uI vI

namespace CategoryTheory.MonoidalCategory.IsFlat

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type uI} [Category.{vI} I]
variable [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
variable [∀ X : C, PreservesColimitsOfShape I (tensorLeft X)]

/-- An exact colimit of flat objects is flat when tensoring in the other variable preserves the
colimit. -/
@[stacks 06YR "flat-object exact-colimit companion"]
theorem colimit_of_exact (F : I ⥤ C) (hF : ∀ i, IsFlat (F.obj i)) :
    IsFlat (colimit F) := sorry

end CategoryTheory.MonoidalCategory.IsFlat
