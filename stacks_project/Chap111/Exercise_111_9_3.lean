module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open Polynomial

/-- Exercise 111.9.3 (1): the length of `ℤ ⧸ Ideal.span {120}` as a `ℤ`-module is `5`. -/
@[stacks 076G]
theorem intMod120_length :
    Module.length ℤ (ℤ ⧸ Ideal.span {(120 : ℤ)}) = (5 : ℕ∞) :=
  sorry

/-- Exercise 111.9.3 (2): the length of `Polynomial ℂ ⧸ Ideal.span {X ^ 100 + X + 1}` as a
`Polynomial ℂ`-module is `100`. -/
@[stacks 076G]
theorem complexPolyMod_length :
    Module.length (Polynomial ℂ)
      (Polynomial ℂ ⧸ Ideal.span {(X ^ 100 + X + 1 : Polynomial ℂ)}) = (100 : ℕ∞) :=
  sorry

/-- Exercise 111.9.3 (3): the length of `Polynomial ℝ ⧸ Ideal.span {X ^ 4 + 2 * X ^ 2 + 1}`
as a `Polynomial ℝ`-module is `2`. -/
@[stacks 076G]
theorem realPolyMod_length :
    Module.length (Polynomial ℝ)
      (Polynomial ℝ ⧸ Ideal.span {(X ^ 4 + 2 * X ^ 2 + 1 : Polynomial ℝ)}) = (2 : ℕ∞) :=
  sorry
