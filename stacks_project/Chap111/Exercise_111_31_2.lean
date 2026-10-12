/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.Hartogs
public import Mathlib.Analysis.Complex.Polynomial.Basic
import StacksCheckRecall

@[expose] public section

noncomputable section

/- Exercise 111.31.2: for `2 ≤ n` and finite `E ⊆ Fin n → ℂ`, every regular function
on the complement `Eᶜ` is a polynomial. -/
@[stacks 0E9E] #check
  (MvPolynomial.isPolynomial_of_isRegular_compl_finite :
    ∀ {n : ℕ} (hn : 2 ≤ n) {E : Set (Fin n → ℂ)} (hE : E.Finite)
      (φ : (Eᶜ : Set (Fin n → ℂ)) → ℂ)
      (hφ : MvPolynomial.IsRegular φ), MvPolynomial.IsPolynomial φ)
