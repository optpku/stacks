/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.PageTower.Preadditive

/-!
# Additive Computations for Homology-Page-Tower Maps

The maps induced on page cycles, boundaries, local homology, recursive stages, and page quotients
are additive in the tower morphism.  These computation statements are kept out of the structural
`PageTower` and `Preadditive` owners so clients can import the algebraic API without unrelated
construction details.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologyPageTower

variable {P Q : HomologyPageTower C}

namespace PageCycle

/-- The page-cycle map induced by a zero tower morphism is zero. -/
@[simp, stacks 011O "zero page-cycle map"]
theorem map_zero (r : ℕ+) : map (0 : P ⟶ Q) r = 0 := sorry

/-- Page-cycle restriction commutes with addition of tower morphisms. -/
@[simp, stacks 011O "addition of page-cycle maps"]
theorem map_add (f g : P ⟶ Q) (r : ℕ+) :
    map (f + g) r = map f r + map g r := sorry

/-- Page-cycle restriction commutes with negation of tower morphisms. -/
@[simp, stacks 011O "negation of page-cycle maps"]
theorem map_neg (f : P ⟶ Q) (r : ℕ+) : map (-f) r = -map f r := sorry

/-- Page-cycle restriction commutes with subtraction of tower morphisms. -/
@[simp, stacks 011O "subtraction of page-cycle maps"]
theorem map_sub (f g : P ⟶ Q) (r : ℕ+) : map (f - g) r = map f r - map g r := sorry

/-- Natural-number scaling commutes with page-cycle restriction. -/
@[simp, stacks 011O "natural scaling of page-cycle maps"]
theorem nsmul_map (n : ℕ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

/-- Integer scaling commutes with page-cycle restriction. -/
@[simp, stacks 011O "integer scaling of page-cycle maps"]
theorem zsmul_map (n : ℤ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

end PageCycle

namespace PageBoundary

/-- The page-boundary map induced by a zero tower morphism is zero. -/
@[simp, stacks 011O "zero page-boundary map"]
theorem map_zero (r : ℕ+) : map (0 : P ⟶ Q) r = 0 := sorry

/-- Page-boundary restriction commutes with addition of tower morphisms. -/
@[simp, stacks 011O "addition of page-boundary maps"]
theorem map_add (f g : P ⟶ Q) (r : ℕ+) :
    map (f + g) r = map f r + map g r := sorry

/-- Page-boundary restriction commutes with negation of tower morphisms. -/
@[simp, stacks 011O "negation of page-boundary maps"]
theorem map_neg (f : P ⟶ Q) (r : ℕ+) : map (-f) r = -map f r := sorry

/-- Page-boundary restriction commutes with subtraction of tower morphisms. -/
@[simp, stacks 011O "subtraction of page-boundary maps"]
theorem map_sub (f g : P ⟶ Q) (r : ℕ+) : map (f - g) r = map f r - map g r := sorry

/-- Natural-number scaling commutes with page-boundary restriction. -/
@[simp, stacks 011O "natural scaling of page-boundary maps"]
theorem nsmul_map (n : ℕ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

/-- Integer scaling commutes with page-boundary restriction. -/
@[simp, stacks 011O "integer scaling of page-boundary maps"]
theorem zsmul_map (n : ℤ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

end PageBoundary

namespace PageHomology

/-- The local page-homology map induced by a zero tower morphism is zero. -/
@[simp, stacks 011O "zero local page-homology map"]
theorem map_zero (r : ℕ+) : map (0 : P ⟶ Q) r = 0 := sorry

/-- Local page homology commutes with addition of tower morphisms. -/
@[simp, stacks 011O "addition of local page-homology maps"]
theorem map_add (f g : P ⟶ Q) (r : ℕ+) :
    map (f + g) r = map f r + map g r := sorry

/-- Local page homology commutes with negation of tower morphisms. -/
@[simp, stacks 011O "negation of local page-homology maps"]
theorem map_neg (f : P ⟶ Q) (r : ℕ+) : map (-f) r = -map f r := sorry

/-- Local page homology commutes with subtraction of tower morphisms. -/
@[simp, stacks 011O "subtraction of local page-homology maps"]
theorem map_sub (f g : P ⟶ Q) (r : ℕ+) : map (f - g) r = map f r - map g r := sorry

/-- Natural-number scaling commutes with local page homology. -/
@[simp, stacks 011O "natural scaling of local page-homology maps"]
theorem nsmul_map (n : ℕ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

/-- Integer scaling commutes with local page homology. -/
@[simp, stacks 011O "integer scaling of local page-homology maps"]
theorem zsmul_map (n : ℤ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

end PageHomology

namespace Cycle

/-- The recursive cycle map induced by a zero tower morphism is zero. -/
@[simp, stacks 011O "zero recursive cycle map"]
theorem map_zero (r : ℕ+) : map (0 : P ⟶ Q) r = 0 := sorry

/-- Recursive cycle restriction commutes with addition of tower morphisms. -/
@[simp, stacks 011O "addition of recursive cycle maps"]
theorem map_add (f g : P ⟶ Q) (r : ℕ+) :
    map (f + g) r = map f r + map g r := sorry

/-- Recursive cycle restriction commutes with negation of tower morphisms. -/
@[simp, stacks 011O "negation of recursive cycle maps"]
theorem map_neg (f : P ⟶ Q) (r : ℕ+) : map (-f) r = -map f r := sorry

/-- Recursive cycle restriction commutes with subtraction of tower morphisms. -/
@[simp, stacks 011O "subtraction of recursive cycle maps"]
theorem map_sub (f g : P ⟶ Q) (r : ℕ+) : map (f - g) r = map f r - map g r := sorry

/-- Natural-number scaling commutes with recursive cycle restriction. -/
@[simp, stacks 011O "natural scaling of recursive cycle maps"]
theorem nsmul_map (n : ℕ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

/-- Integer scaling commutes with recursive cycle restriction. -/
@[simp, stacks 011O "integer scaling of recursive cycle maps"]
theorem zsmul_map (n : ℤ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

end Cycle

namespace Boundary

/-- The recursive boundary map induced by a zero tower morphism is zero. -/
@[simp, stacks 011O "zero recursive boundary map"]
theorem map_zero (r : ℕ+) : map (0 : P ⟶ Q) r = 0 := sorry

/-- Recursive boundary restriction commutes with addition of tower morphisms. -/
@[simp, stacks 011O "addition of recursive boundary maps"]
theorem map_add (f g : P ⟶ Q) (r : ℕ+) :
    map (f + g) r = map f r + map g r := sorry

/-- Recursive boundary restriction commutes with negation of tower morphisms. -/
@[simp, stacks 011O "negation of recursive boundary maps"]
theorem map_neg (f : P ⟶ Q) (r : ℕ+) : map (-f) r = -map f r := sorry

/-- Recursive boundary restriction commutes with subtraction of tower morphisms. -/
@[simp, stacks 011O "subtraction of recursive boundary maps"]
theorem map_sub (f g : P ⟶ Q) (r : ℕ+) : map (f - g) r = map f r - map g r := sorry

/-- Natural-number scaling commutes with recursive boundary restriction. -/
@[simp, stacks 011O "natural scaling of recursive boundary maps"]
theorem nsmul_map (n : ℕ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

/-- Integer scaling commutes with recursive boundary restriction. -/
@[simp, stacks 011O "integer scaling of recursive boundary maps"]
theorem zsmul_map (n : ℤ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

end Boundary

namespace PageQuotient

/-- The recursive page-quotient map induced by a zero tower morphism is zero. -/
@[simp, stacks 011O "zero recursive page-quotient map"]
theorem map_zero (r : ℕ+) : map (0 : P ⟶ Q) r = 0 := sorry

/-- Recursive page quotients commute with addition of tower morphisms. -/
@[simp, stacks 011O "addition of recursive page-quotient maps"]
theorem map_add (f g : P ⟶ Q) (r : ℕ+) :
    map (f + g) r = map f r + map g r := sorry

/-- Recursive page quotients commute with negation of tower morphisms. -/
@[simp, stacks 011O "negation of recursive page-quotient maps"]
theorem map_neg (f : P ⟶ Q) (r : ℕ+) : map (-f) r = -map f r := sorry

/-- Recursive page quotients commute with subtraction of tower morphisms. -/
@[simp, stacks 011O "subtraction of recursive page-quotient maps"]
theorem map_sub (f g : P ⟶ Q) (r : ℕ+) : map (f - g) r = map f r - map g r := sorry

/-- Natural-number scaling commutes with recursive page quotients. -/
@[simp, stacks 011O "natural scaling of recursive page-quotient maps"]
theorem nsmul_map (n : ℕ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

/-- Integer scaling commutes with recursive page quotients. -/
@[simp, stacks 011O "integer scaling of recursive page-quotient maps"]
theorem zsmul_map (n : ℤ) (f : P ⟶ Q) (r : ℕ+) : map (n • f) r = n • map f r := sorry

end PageQuotient

end HomologyPageTower

end CategoryTheory
