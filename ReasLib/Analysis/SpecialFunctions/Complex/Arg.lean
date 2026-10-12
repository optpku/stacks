/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Finite.Defs

@[expose] public section

universe u

namespace Complex

/-- Every finite family of complex numbers admits a common positive natural power
whose principal arguments have absolute value below any prescribed positive tolerance. -/
theorem exists_pow_abs_arg_lt {ι : Type u} [Finite ι] (α : ι → ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ k : ℕ, 1 ≤ k ∧ ∀ i, |Complex.arg (α i ^ k)| < ε := sorry

end Complex
