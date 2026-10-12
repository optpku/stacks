/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open Polynomial

namespace AlgebraicGeometry.ProjectiveSpace

/-- Exercise 111.45.4: In Situation 111.45.1, if `2 ≤ n`, there exists a coherent
`𝒪`-module on `scheme k n` whose Hilbert polynomial is `C (1 / 2 : ℚ) * X ^ 2 + C (1 / 2 : ℚ) * X - 1`. -/
@[stacks 0DCH]
theorem exists_isHilbertPolynomial (k : Type u) [Field k] (n : ℕ) (hn : 2 ≤ n) :
    ∃ (ℱ : (scheme k n).Modules) (_ : ℱ.IsCoherent),
      IsHilbertPolynomial k n ℱ (C (1 / 2 : ℚ) * X ^ 2 + C (1 / 2 : ℚ) * X - 1) :=
  sorry

/-- The Hilbert polynomial of a coherent module on `scheme k n` is
`C (1 / 2 : ℚ) * X ^ 2 + C (1 / 2 : ℚ) * X - 1` if and only if its Euler-characteristic
function is `t ↦ (t : ℚ) ^ 2 / 2 + (t : ℚ) / 2 - 1`. -/
theorem isHilbertPolynomial_eval_iff {k : Type u} [Field k] {n : ℕ}
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] :
    IsHilbertPolynomial k n ℱ (C (1 / 2 : ℚ) * X ^ 2 + C (1 / 2 : ℚ) * X - 1) ↔
      ∀ t : ℤ, (hilbertPolynomial k n ℱ t : ℚ) = (t : ℚ) ^ 2 / 2 + (t : ℚ) / 2 - 1 :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
