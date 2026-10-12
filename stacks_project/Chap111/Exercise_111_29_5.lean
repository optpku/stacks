/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_29_5_Specialize
public import stacks_project.Chap111.Exercise_111_29_5_Adjoin
import StacksCheckRecall

open Polynomial
open scoped Polynomial.Bivariate

/-!
# Exercise 111.29.5

With `h` monic of positive degree, `A = ℤ[X]` and
`B = AdjoinRoot (adjoinRootPoly h)` as in the preceding remark, write
`f_p = intEvalXPowMod p f` and `Norm_{B_p / A_p}(g_p) = algebraNormSpecialize h p g`.
-/

/- Exercise 111.29.5 (1): there exist a monic polynomial `h` of positive degree and a
bivariate polynomial `g` such that no bivariate polynomial `f` interpolates the norms
`algebraNormSpecialize h p g` as `intEvalXPowMod p f` for every prime `p`. -/
@[stacks 02ES] #check
  (Polynomial.exists_not_eq_algebraNormSpecialize :
    ∃ (h : ℤ[X]), h.Monic ∧ 0 < h.natDegree ∧ ∃ (g : ℤ[X][Y]),
      ¬ ∃ (f : ℤ[X][Y]), ∀ (p : ℕ) [Fact p.Prime],
        Polynomial.intEvalXPowMod p f = Polynomial.algebraNormSpecialize h p g)

/- Exercise 111.29.5 (2): for every monic `h` of positive degree and every nonzero
bivariate `g`, there exists a nonzero bivariate `f` such that
`algebraNormSpecialize h p g` divides `intEvalXPowMod p f` for every prime `p`. -/
@[stacks 02ES] #check
  (Polynomial.exists_dvd_algebraNormSpecialize :
    ∀ (h : ℤ[X]), h.Monic → 0 < h.natDegree → ∀ (g : ℤ[X][Y]), g ≠ 0 →
      ∃ (f : ℤ[X][Y]), f ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime],
        Polynomial.algebraNormSpecialize h p g ∣ Polynomial.intEvalXPowMod p f)

/- Exercise 111.29.5 (3): discuss the relevance of these assertions to Exercises 6
and 7 of the previous set, where norm behavior is compared with integral polynomial
interpolation and divisibility. -/
