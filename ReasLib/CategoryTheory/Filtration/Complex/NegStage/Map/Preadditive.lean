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
theorem mapApp_zero (n : ℕ) : mapApp (0 : K ⟶ L) n = 0 := by
  exact (FilteredComplex.Stage.functor (index n)).map_zero K L

/-- Negative-stage component maps preserve addition. -/
@[simp, stacks 0D8Z "addition computation for negative-stage component maps"]
theorem mapApp_add (f g : K ⟶ L) (n : ℕ) :
    mapApp (f + g) n = mapApp f n + mapApp g n := by
  exact (FilteredComplex.Stage.functor (index n)).map_add

/-- Negative-stage component maps preserve negation. -/
@[simp, stacks 0D8Z "negation computation for negative-stage component maps"]
theorem mapApp_neg (f : K ⟶ L) (n : ℕ) : mapApp (-f) n = -mapApp f n := by
  exact (FilteredComplex.Stage.functor (index n)).map_neg

/-- Negative-stage component maps preserve subtraction. -/
@[simp, stacks 0D8Z "subtraction computation for negative-stage component maps"]
theorem mapApp_sub (f g : K ⟶ L) (n : ℕ) :
    mapApp (f - g) n = mapApp f n - mapApp g n := by
  exact (FilteredComplex.Stage.functor (index n)).map_sub

/-- Negative-stage component maps preserve natural scalar multiplication. -/
@[simp, stacks 0D8Z "natural-scalar computation for negative-stage component maps"]
theorem mapApp_nsmul (n : ℕ) (f : K ⟶ L) (i : ℕ) :
    mapApp (n • f) i = n • mapApp f i := by
  exact (FilteredComplex.Stage.functor (index i)).map_nsmul

/-- Negative-stage component maps preserve integer scalar multiplication. -/
@[simp, stacks 0D8Z "integer-scalar computation for negative-stage component maps"]
theorem mapApp_zsmul (n : ℤ) (f : K ⟶ L) (i : ℕ) :
    mapApp (n • f) i = n • mapApp f i := by
  exact (FilteredComplex.Stage.functor (index i)).map_zsmul

/-- The map of negative-stage diagrams sends zero to zero. -/
@[simp, stacks 0D8Z "zero computation for negative-stage diagram maps"]
theorem map_zero : map (0 : K ⟶ L) = 0 := by
  apply NatTrans.ext
  funext n
  exact mapApp_zero n

/-- Maps of negative-stage diagrams preserve addition. -/
@[simp, stacks 0D8Z "addition computation for negative-stage diagram maps"]
theorem map_add (f g : K ⟶ L) : map (f + g) = map f + map g := by
  apply NatTrans.ext
  funext n
  exact mapApp_add f g n

/-- Maps of negative-stage diagrams preserve negation. -/
@[simp, stacks 0D8Z "negation computation for negative-stage diagram maps"]
theorem map_neg (f : K ⟶ L) : map (-f) = -map f := by
  apply NatTrans.ext
  funext n
  exact mapApp_neg f n

/-- Maps of negative-stage diagrams preserve subtraction. -/
@[simp, stacks 0D8Z "subtraction computation for negative-stage diagram maps"]
theorem map_sub (f g : K ⟶ L) : map (f - g) = map f - map g := by
  apply NatTrans.ext
  funext n
  exact mapApp_sub f g n

/-- Maps of negative-stage diagrams preserve natural scalar multiplication. -/
@[simp, stacks 0D8Z "natural-scalar computation for negative-stage diagram maps"]
theorem map_nsmul (n : ℕ) (f : K ⟶ L) : map (n • f) = n • map f := by
  apply NatTrans.ext
  funext i
  exact mapApp_nsmul n f i

/-- Maps of negative-stage diagrams preserve integer scalar multiplication. -/
@[simp, stacks 0D8Z "integer-scalar computation for negative-stage diagram maps"]
theorem map_zsmul (n : ℤ) (f : K ⟶ L) : map (n • f) = n • map f := by
  apply NatTrans.ext
  funext i
  exact mapApp_zsmul n f i

end CategoryTheory.FilteredComplex.NegStage
