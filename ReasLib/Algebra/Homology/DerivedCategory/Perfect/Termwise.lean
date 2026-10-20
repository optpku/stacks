/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise perfect bounded complexes

This file records the passage from a bounded cochain complex whose terms are perfect modules to
a perfect object of the derived category.

@stack 066T
-/

@[expose] public section

open CategoryTheory

universe u

namespace CochainComplex.Bounded

variable {R : Type u} [Ring R]

/-- Lemma 15.75.6 (066T): a bounded cochain complex of perfect `R`-modules represents a perfect
object of `DerivedCategory (ModuleCat R)`. -/
@[stacks 066T "bounded complexes with perfect terms"]
theorem isPerfect (K : CochainComplex.Bounded (ModuleCat R))
    (hK : ∀ i : ℤ, (K.obj.X i).IsPerfect) :
    (DerivedCategory.Q.obj K.obj).IsPerfect := sorry

end CochainComplex.Bounded
