module

import ReasLib.Analysis.SpecialFunctions.Complex.Arg
import StacksCheckRecall

universe u

/- Exercise 64.23.2: let `α : ι → ℂ` be a finite family of complex numbers.
Then for any conic sector containing the positive real axis of the form
`C_ε = {z | |arg z| < ε}` with `0 < ε` (equivalently `arg ⁻¹' Ioo (-ε) ε`),
there exists an integer `k ≥ 1` such that `α i ^ k ∈ C_ε` for every `i`. -/
@[stacks 03V9] #check (Complex.exists_pow_abs_arg_lt :
  ∀ {ι : Type u} [Finite ι] (α : ι → ℂ) {ε : ℝ},
    0 < ε → ∃ k : ℕ, 1 ≤ k ∧ ∀ i, |Complex.arg (α i ^ k)| < ε)
