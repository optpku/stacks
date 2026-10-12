/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace LindemannWeierstrass

-- Declarations for this item will be appended below by the statement pipeline.

-- The source-facing subset expansion is the canonical `Finset.prod_one_add` identity, with each
-- subsetwise product of exponentials rewritten by `Complex.exp_sum`.

/-- Lemma PI-04: for every finite family `a : Fin n → ℂ`,
expanding `∏ i, (1 + Complex.exp (a i))` over subsets of `Fin n`
gives a sum of exponentials of the corresponding partial sums. -/
theorem prod_one_add_exp_eq_sum_powerset_exp_sum (n : ℕ) (a : Fin n → ℂ) :
    ∏ i, (1 + Complex.exp (a i)) =
      ((Finset.univ : Finset (Fin n)).powerset).sum (fun s ↦ Complex.exp (s.sum a)) := by
  classical
  rw [Finset.prod_one_add]
  refine Finset.sum_congr rfl fun s _hs ↦ ?_
  simpa using (Complex.exp_sum s a).symm

end LindemannWeierstrass
