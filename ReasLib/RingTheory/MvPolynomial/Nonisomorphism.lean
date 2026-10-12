/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

universe u

namespace MvPolynomial

/-- Polynomial algebras on consecutive positive finite sets of variables are not
equivalent as algebras over their coefficient field. -/
theorem not_algEquiv_fin_succ (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) :
    ¬ Nonempty (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k) := sorry

end MvPolynomial
