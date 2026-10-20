/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.NegStage.Map
public import ReasLib.CategoryTheory.Filtration.Complex.NegStage.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive computation for negative-stage maps

This leaf exposes the additive calculations for component and bundled maps of the negative-stage
facade.  The category-independent identity and composition rules remain in `NegStage.Map`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.NegStage

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {K L : FilteredComplex A}

/-- A negative-stage component map sends zero to zero. -/
@[simp, stacks 0D8Z "zero computation for negative-stage component maps"]
theorem mapApp_zero (n : ℕ) : mapApp (0 : K ⟶ L) n = 0 := sorry

/-- Negative-stage component maps preserve addition. -/
@[simp, stacks 0D8Z "addition computation for negative-stage component maps"]
theorem mapApp_add (f g : K ⟶ L) (n : ℕ) :
    mapApp (f + g) n = mapApp f n + mapApp g n := sorry

/-- Negative-stage component maps preserve negation. -/
@[simp, stacks 0D8Z "negation computation for negative-stage component maps"]
theorem mapApp_neg (f : K ⟶ L) (n : ℕ) : mapApp (-f) n = -mapApp f n := sorry

/-- Negative-stage component maps preserve subtraction. -/
@[simp, stacks 0D8Z "subtraction computation for negative-stage component maps"]
theorem mapApp_sub (f g : K ⟶ L) (n : ℕ) :
    mapApp (f - g) n = mapApp f n - mapApp g n := sorry

/-- Negative-stage component maps preserve natural scalar multiplication. -/
@[simp, stacks 0D8Z "natural-scalar computation for negative-stage component maps"]
theorem mapApp_nsmul (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    mapApp (n • f) i = n • mapApp f i := sorry

/-- Negative-stage component maps preserve integer scalar multiplication. -/
@[simp, stacks 0D8Z "integer-scalar computation for negative-stage component maps"]
theorem mapApp_zsmul (n : ℤ) (f : K ⟶ L) (i : ℕ) :
    mapApp (n • f) i = n • mapApp f i := sorry

/-- The map of negative-stage diagrams sends zero to zero. -/
@[simp, stacks 0D8Z "zero computation for negative-stage diagram maps"]
theorem map_zero : map (0 : K ⟶ L) = 0 := sorry

/-- Maps of negative-stage diagrams preserve addition. -/
@[simp, stacks 0D8Z "addition computation for negative-stage diagram maps"]
theorem map_add (f g : K ⟶ L) : map (f + g) = map f + map g := sorry

/-- Maps of negative-stage diagrams preserve negation. -/
@[simp, stacks 0D8Z "negation computation for negative-stage diagram maps"]
theorem map_neg (f : K ⟶ L) : map (-f) = -map f := sorry

/-- Maps of negative-stage diagrams preserve subtraction. -/
@[simp, stacks 0D8Z "subtraction computation for negative-stage diagram maps"]
theorem map_sub (f g : K ⟶ L) : map (f - g) = map f - map g := sorry

/-- Maps of negative-stage diagrams preserve natural scalar multiplication. -/
@[simp, stacks 0D8Z "natural-scalar computation for negative-stage diagram maps"]
theorem map_nsmul (n : ℕ) (f : K ⟶ L) : map (n • f) = n • map f := sorry

/-- Maps of negative-stage diagrams preserve integer scalar multiplication. -/
@[simp, stacks 0D8Z "integer-scalar computation for negative-stage diagram maps"]
theorem map_zsmul (n : ℤ) (f : K ⟶ L) : map (n • f) = n • map f := sorry

end CategoryTheory.FilteredComplex.NegStage
