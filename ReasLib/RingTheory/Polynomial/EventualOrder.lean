/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial Degree from Eventual Order

Polynomial degree can be read from eventual inequalities along any sequence
tending to infinity.  The rational natural-cast specialization is the form
used by Hilbert and Hilbert--Samuel polynomial arguments.
-/

@[expose] public section

open Filter

universe u v

namespace Polynomial

variable {K : Type u} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [OrderTopology K]
variable {ι : Type v} {l : Filter ι} {f : ι → K}

/-- If `f` tends to infinity and `P(f i)` is eventually nonnegative and at
most `Q(f i)`, then `P` has degree at most `Q`. -/
theorem degree_le_of_eventually_nonneg_le_comp {P Q : K[X]}
    (hf : Tendsto f l atTop)
    (hPQ : ∀ᶠ i in l, 0 ≤ P.eval (f i) ∧ P.eval (f i) ≤ Q.eval (f i)) :
    P.degree ≤ Q.degree := sorry

/-- A rational polynomial that is eventually nonnegative and bounded above
by another polynomial on natural-number inputs has no larger degree. -/
theorem degree_le_of_eventually_nonneg_le_natCast {P Q : ℚ[X]}
    (hPQ : ∀ᶠ n : ℕ in atTop,
      0 ≤ P.eval (n : ℚ) ∧ P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.degree ≤ Q.degree := sorry

end Polynomial
