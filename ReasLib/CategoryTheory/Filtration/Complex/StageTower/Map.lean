/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.StageTower.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive computation for filtration-stage towers

This leaf records the componentwise and bundled additive computations for maps of the integer
filtration-stage tower.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.StageTower

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : FilteredComplex C}

/-- A component of an integer stage-tower map sends zero to zero. -/
@[simp, stacks 012L "zero computation for integer stage-tower components"]
theorem map_app_zero (i : ℤᵒᵖ) : (map (0 : K ⟶ L)).app i = 0 := by
  exact (FilteredComplex.Stage.functor i.unop).map_zero K L

/-- Components of integer stage-tower maps preserve addition. -/
@[simp, stacks 012L "addition computation for integer stage-tower components"]
theorem map_app_add (f g : K ⟶ L) (i : ℤᵒᵖ) :
    (map (f + g)).app i = (map f).app i + (map g).app i := by
  exact (FilteredComplex.Stage.functor i.unop).map_add

/-- Components of integer stage-tower maps preserve negation. -/
@[simp, stacks 012L "negation computation for integer stage-tower components"]
theorem map_app_neg (f : K ⟶ L) (i : ℤᵒᵖ) :
    (map (-f)).app i = -(map f).app i := by
  exact (FilteredComplex.Stage.functor i.unop).map_neg

/-- Components of integer stage-tower maps preserve subtraction. -/
@[simp, stacks 012L "subtraction computation for integer stage-tower components"]
theorem map_app_sub (f g : K ⟶ L) (i : ℤᵒᵖ) :
    (map (f - g)).app i = (map f).app i - (map g).app i := by
  exact (FilteredComplex.Stage.functor i.unop).map_sub

/-- Components of integer stage-tower maps preserve natural scalar multiplication. -/
@[simp, stacks 012L "natural-scalar computation for integer stage-tower components"]
theorem map_app_nsmul (n : ℕ) (f : K ⟶ L) (i : ℤᵒᵖ) :
    (map (n • f)).app i = n • (map f).app i := by
  exact (FilteredComplex.Stage.functor i.unop).map_nsmul

/-- Components of integer stage-tower maps preserve integer scalar multiplication. -/
@[simp, stacks 012L "integer-scalar computation for integer stage-tower components"]
theorem map_app_zsmul (n : ℤ) (f : K ⟶ L) (i : ℤᵒᵖ) :
    (map (n • f)).app i = n • (map f).app i := by
  exact (FilteredComplex.Stage.functor i.unop).map_zsmul

/-- The integer stage-tower map sends zero to zero. -/
@[simp, stacks 012L "zero computation for integer stage-tower maps"]
theorem map_zero : map (0 : K ⟶ L) = 0 := by
  apply NatTrans.ext
  funext i
  exact map_app_zero i

/-- Integer stage-tower maps preserve addition. -/
@[simp, stacks 012L "addition computation for integer stage-tower maps"]
theorem map_add (f g : K ⟶ L) : map (f + g) = map f + map g := by
  apply NatTrans.ext
  funext i
  exact map_app_add f g i

/-- Integer stage-tower maps preserve negation. -/
@[simp, stacks 012L "negation computation for integer stage-tower maps"]
theorem map_neg (f : K ⟶ L) : map (-f) = -map f := by
  apply NatTrans.ext
  funext i
  exact map_app_neg f i

/-- Integer stage-tower maps preserve subtraction. -/
@[simp, stacks 012L "subtraction computation for integer stage-tower maps"]
theorem map_sub (f g : K ⟶ L) : map (f - g) = map f - map g := by
  apply NatTrans.ext
  funext i
  exact map_app_sub f g i

/-- Integer stage-tower maps preserve natural scalar multiplication. -/
@[simp, stacks 012L "natural-scalar computation for integer stage-tower maps"]
theorem map_nsmul (n : ℕ) (f : K ⟶ L) : map (n • f) = n • map f := by
  apply NatTrans.ext
  funext i
  exact map_app_nsmul n f i

/-- Integer stage-tower maps preserve integer scalar multiplication. -/
@[simp, stacks 012L "integer-scalar computation for integer stage-tower maps"]
theorem map_zsmul (n : ℤ) (f : K ⟶ L) : map (n • f) = n • map f := by
  apply NatTrans.ext
  funext i
  exact map_app_zsmul n f i

end CategoryTheory.FilteredComplex.StageTower
