/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GlobalDimension.Basic

@[expose] public section

/-!
# Global Dimension from Ideal Quotients

For commutative rings, cyclic modules form a test family for a uniform projective-dimension
bound. The constructor and its characteristic theorem live with the global-dimension owner.
-/

open CategoryTheory

universe u

namespace HasGlobalDimensionLE

variable {R : Type u} [CommRing R]

/-- Stacks 065T: a common projective-dimension bound for all ideal quotients `R ⧸ I` is a
global-dimension bound for `R`. -/
@[stacks 065T "ideal-quotient constructor"]
theorem of_idealQuotients {n : ℕ}
    (h : ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n) :
    HasGlobalDimensionLE R n := sorry

/-- Stacks 065T: global dimension at most `n` can be tested on the cyclic modules `R ⧸ I`. -/
@[stacks 065T "ideal-quotient characterization"]
theorem iff_idealQuotients (n : ℕ) :
    HasGlobalDimensionLE R n ↔
      ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n := sorry

end HasGlobalDimensionLE
