/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Triangulated
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness from bounded cohomology

A bounded derived module object is perfect when each of its cohomology modules is perfect.  The
statement uses the canonical bounded derived category and its restricted cohomology functors.

@stack 066U
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DerivedCategory.IsPerfect

variable {R : Type u} [Ring R]

/-- Lemma 15.75.7 (066U): a bounded derived object with perfect cohomology modules is perfect. -/
@[stacks 066U "bounded object with perfect cohomology"]
theorem of_bounded_of_homology
    (K : DerivedCategory.Bounded (ModuleCat R))
    (hH : ∀ i : ℤ,
      ((DerivedCategory.Bounded.homologyFunctor (ModuleCat R) i).obj K).IsPerfect) :
    K.obj.IsPerfect := sorry

end DerivedCategory.IsPerfect
