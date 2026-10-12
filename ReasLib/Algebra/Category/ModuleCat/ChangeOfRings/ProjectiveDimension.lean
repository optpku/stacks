/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective dimension under restriction of scalars

This leaf owns the resolution-theoretic bound that is independent of locality, finiteness, and
perfect derived models.  A projective resolution of the regular `S`-module over `R`, followed by a
projective resolution over `S`, gives the additive bound after restriction along `f : R →+* S`.
@stack 0929
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace ModuleCat.RestrictScalars

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- Stacks 0929: bounded projective dimensions add under restriction of scalars. -/
@[stacks 0929 "projective-dimension bound under restriction of scalars"]
theorem hasProjectiveDimensionLE_add
    (f : R →+* S) (M : ModuleCat.{w} S) {a b : ℕ}
    (hS : HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) a)
    (hM : HasProjectiveDimensionLE M b) :
    HasProjectiveDimensionLE ((ModuleCat.restrictScalars f).obj M) (a + b) := sorry

/-- The same additive bound expressed directly in the canonical `projectiveDimension` invariant. -/
@[stacks 0929 "projective-dimension inequality under restriction of scalars"]
theorem projectiveDimension_le_add
    (f : R →+* S) (M : ModuleCat.{w} S) {a b : ℕ}
    (hS : projectiveDimension
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ≤ a)
    (hM : projectiveDimension M ≤ b) :
    projectiveDimension ((ModuleCat.restrictScalars f).obj M) ≤ a + b := sorry

/-- Finite projective dimension is preserved by restriction when the regular target module and the
given module both have finite projective dimension. -/
@[stacks 0929 "finite projective dimension under restriction of scalars"]
theorem projectiveDimension_ne_top
    (f : R →+* S) (M : ModuleCat.{w} S)
    (hS : projectiveDimension
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ≠ ⊤)
    (hM : projectiveDimension M ≠ ⊤) :
    projectiveDimension ((ModuleCat.restrictScalars f).obj M) ≠ ⊤ := sorry

end ModuleCat.RestrictScalars
