/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

universe u

@[expose] public section

namespace MvPolynomial

/-- A tuple `α` is a nontrivial solution of `f` when it is not the zero tuple
and evaluates `f` to zero. -/
structure IsNontrivialSolution {K : Type u} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (α : Fin n → K) : Prop where
  nonzero : α ≠ 0
  eval_eq_zero : MvPolynomial.eval α f = 0

/-- Construct a nontrivial solution from its nonzero and vanishing conditions. -/
def IsNontrivialSolution.of {K : Type u} [CommSemiring K] {n : ℕ}
    {f : MvPolynomial (Fin n) K} {α : Fin n → K}
    (h_nonzero : α ≠ 0) (h_eval : MvPolynomial.eval α f = 0) :
    IsNontrivialSolution f α := ⟨h_nonzero, h_eval⟩

/-- The defining conditions for a nontrivial solution of a multivariate polynomial. -/
theorem isNontrivialSolution_iff {K : Type u} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (α : Fin n → K) :
    IsNontrivialSolution f α ↔ α ≠ 0 ∧ MvPolynomial.eval α f = 0 := sorry

/-- The coordinate formulation of a nontrivial solution's nonzero condition. -/
theorem isNontrivialSolution_iff_exists_ne_zero {K : Type u} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (α : Fin n → K) :
    IsNontrivialSolution f α ↔
      (∃ i : Fin n, α i ≠ 0) ∧ MvPolynomial.eval α f = 0 := sorry

end MvPolynomial
