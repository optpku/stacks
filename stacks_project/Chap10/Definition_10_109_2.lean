/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import StacksCheckRecall

/-!
# Projective Dimension

@stack 00O4
-/

@[expose] public section

universe u v

variable {R : Type u} [Ring R]

/- Definition 10.109.2 (00O4): finite projective dimension and projective dimension are represented
by the canonical invariant `CategoryTheory.projectiveDimension`. Its value is different from `⊤`
exactly when there is a finite natural-number bound. Mathlib refines the textbook convention by
assigning `⊥` to the zero module. -/
@[stacks 00O4 "projective-dimension invariant"]
#check (CategoryTheory.projectiveDimension : ModuleCat.{v} R → WithBot ℕ∞)

/- The finite-projective-dimension criterion is the non-top characterization of the invariant. -/
@[stacks 00O4 "finite projective dimension"]
#check @CategoryTheory.projectiveDimension_ne_top_iff

@[stacks 00O4 "bounded projective dimension"]
#check @CategoryTheory.projectiveDimension_le_iff

@[stacks 00O4 "zero-module projective dimension"]
#check @CategoryTheory.projectiveDimension_eq_bot_iff
