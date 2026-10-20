/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.StageSequence.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive computation for filtration-stage sequences

This leaf exposes the componentwise and bundled additive computations for maps of stage
sequences.  The construction of the sequence and its additive instance remain in their neutral
owner files.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.StageSequence

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : FilteredComplex C} (p : ℕ → ℤ) (hp : Antitone p)

/-- The component of a selected stage-sequence map sends zero to zero. -/
@[simp, stacks 0D8Z "zero computation for filtration-stage sequence components"]
theorem map_app_zero (n : ℕ) : (map (0 : K ⟶ L) p hp).app n = 0 := sorry

/-- Components of selected stage-sequence maps preserve addition. -/
@[simp, stacks 0D8Z "addition computation for filtration-stage sequence components"]
theorem map_app_add (f g : K ⟶ L) (n : ℕ) :
    (map (f + g) p hp).app n = (map f p hp).app n + (map g p hp).app n := sorry

/-- Components of selected stage-sequence maps preserve negation. -/
@[simp, stacks 0D8Z "negation computation for filtration-stage sequence components"]
theorem map_app_neg (f : K ⟶ L) (n : ℕ) :
    (map (-f) p hp).app n = -(map f p hp).app n := sorry

/-- Components of selected stage-sequence maps preserve subtraction. -/
@[simp, stacks 0D8Z "subtraction computation for filtration-stage sequence components"]
theorem map_app_sub (f g : K ⟶ L) (n : ℕ) :
    (map (f - g) p hp).app n = (map f p hp).app n - (map g p hp).app n := sorry

/-- Components of selected stage-sequence maps preserve natural scalar multiplication. -/
@[simp, stacks 0D8Z "natural-scalar computation for filtration-stage sequence components"]
theorem map_app_nsmul (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    (map (n • f) p hp).app i = n • (map f p hp).app i := sorry

/-- Components of selected stage-sequence maps preserve integer scalar multiplication. -/
@[simp, stacks 0D8Z "integer-scalar computation for filtration-stage sequence components"]
theorem map_app_zsmul (n : ℤ) (f : K ⟶ L) (i : ℕ) :
    (map (n • f) p hp).app i = n • (map f p hp).app i := sorry

/-- The selected stage-sequence map sends zero to zero. -/
@[simp, stacks 0D8Z "zero computation for filtration-stage sequence maps"]
theorem map_zero : map (0 : K ⟶ L) p hp = 0 := sorry

/-- Selected stage-sequence maps preserve addition. -/
@[simp, stacks 0D8Z "addition computation for filtration-stage sequence maps"]
theorem map_add (f g : K ⟶ L) : map (f + g) p hp = map f p hp + map g p hp := sorry

/-- Selected stage-sequence maps preserve negation. -/
@[simp, stacks 0D8Z "negation computation for filtration-stage sequence maps"]
theorem map_neg (f : K ⟶ L) : map (-f) p hp = -map f p hp := sorry

/-- Selected stage-sequence maps preserve subtraction. -/
@[simp, stacks 0D8Z "subtraction computation for filtration-stage sequence maps"]
theorem map_sub (f g : K ⟶ L) : map (f - g) p hp = map f p hp - map g p hp := sorry

/-- Selected stage-sequence maps preserve natural scalar multiplication. -/
@[simp, stacks 0D8Z "natural-scalar computation for filtration-stage sequence maps"]
theorem map_nsmul (n : ℕ) (f : K ⟶ L) : map (n • f) p hp = n • map f p hp := sorry

/-- Selected stage-sequence maps preserve integer scalar multiplication. -/
@[simp, stacks 0D8Z "integer-scalar computation for filtration-stage sequence maps"]
theorem map_zsmul (n : ℤ) (f : K ⟶ L) : map (n • f) p hp = n • map f p hp := sorry

end CategoryTheory.FilteredComplex.StageSequence
