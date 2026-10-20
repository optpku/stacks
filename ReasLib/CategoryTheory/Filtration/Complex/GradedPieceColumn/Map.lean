/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors.Map
public import ReasLib.CategoryTheory.Filtration.Complex.GradedPieceColumn.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation for maps of graded-piece columns

This leaf exposes evaluation and additive computation for the map on a fixed reindexed
graded-piece column.  The column construction and homology comparison remain in the base file.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.GradedPiece.Column

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
variable {K L : FilteredComplex C}

/-- Evaluating the fixed-column functor gives the corresponding reindexed graded-piece
complex. -/
@[simp, stacks 012M "object of the graded-piece column functor"]
theorem functor_obj (K : FilteredComplex C) (p : ℤ) :
    (functor (C := C) p).obj K = complex K p := sorry

/-- The map of the fixed-column functor is the reindexed graded-piece column map. -/
@[simp, stacks 012M "map of the graded-piece column functor"]
theorem functor_map (f : K ⟶ L) (p : ℤ) :
    (functor (C := C) p).map f = map f p := sorry

/-- Evaluating a column map gives the corresponding reindexed graded-piece map. -/
@[simp, stacks 012M "component of a graded-piece column map"]
theorem map_f (f : K ⟶ L) (p q : ℤ) :
    (map f p).f q = (gradedPieceMap f p).f (p + q) := sorry

/-- A component of a graded-piece column map sends zero to zero. -/
@[simp, stacks 012M "zero computation for graded-piece column components"]
theorem map_f_zero (p q : ℤ) : (map (0 : K ⟶ L) p).f q = 0 := sorry

/-- Components of graded-piece column maps preserve addition. -/
@[simp, stacks 012M "addition computation for graded-piece column components"]
theorem map_f_add (f g : K ⟶ L) (p q : ℤ) :
    (map (f + g) p).f q = (map f p).f q + (map g p).f q := sorry

/-- Components of graded-piece column maps preserve negation. -/
@[simp, stacks 012M "negation computation for graded-piece column components"]
theorem map_f_neg (f : K ⟶ L) (p q : ℤ) :
    (map (-f) p).f q = -(map f p).f q := sorry

/-- Components of graded-piece column maps preserve subtraction. -/
@[simp, stacks 012M "subtraction computation for graded-piece column components"]
theorem map_f_sub (f g : K ⟶ L) (p q : ℤ) :
    (map (f - g) p).f q = (map f p).f q - (map g p).f q := sorry

/-- Components of graded-piece column maps preserve natural scalar multiplication. -/
@[simp, stacks 012M "natural-scalar computation for graded-piece column components"]
theorem map_f_nsmul (n : ℕ) (f : K ⟶ L) (p q : ℤ) :
    (map (n • f) p).f q = n • (map f p).f q := sorry

/-- Components of graded-piece column maps preserve integer scalar multiplication. -/
@[simp, stacks 012M "integer-scalar computation for graded-piece column components"]
theorem map_f_zsmul (n : ℤ) (f : K ⟶ L) (p q : ℤ) :
    (map (n • f) p).f q = n • (map f p).f q := sorry

/-- A fixed graded-piece column map sends zero to zero. -/
@[simp, stacks 012M "zero computation for graded-piece column maps"]
theorem map_zero (p : ℤ) : map (0 : K ⟶ L) p = 0 := sorry

/-- Fixed graded-piece column maps preserve addition. -/
@[simp, stacks 012M "addition computation for graded-piece column maps"]
theorem map_add (f g : K ⟶ L) (p : ℤ) : map (f + g) p = map f p + map g p := sorry

/-- Fixed graded-piece column maps preserve negation. -/
@[simp, stacks 012M "negation computation for graded-piece column maps"]
theorem map_neg (f : K ⟶ L) (p : ℤ) : map (-f) p = -map f p := sorry

/-- Fixed graded-piece column maps preserve subtraction. -/
@[simp, stacks 012M "subtraction computation for graded-piece column maps"]
theorem map_sub (f g : K ⟶ L) (p : ℤ) : map (f - g) p = map f p - map g p := sorry

/-- Fixed graded-piece column maps preserve natural scalar multiplication. -/
@[simp, stacks 012M "natural-scalar computation for graded-piece column maps"]
theorem map_nsmul (n : ℕ) (f : K ⟶ L) (p : ℤ) : map (n • f) p = n • map f p := sorry

/-- Fixed graded-piece column maps preserve integer scalar multiplication. -/
@[simp, stacks 012M "integer-scalar computation for graded-piece column maps"]
theorem map_zsmul (n : ℤ) (f : K ⟶ L) (p : ℤ) : map (n • f) p = n • map f p := sorry

end CategoryTheory.FilteredComplex.GradedPiece.Column
