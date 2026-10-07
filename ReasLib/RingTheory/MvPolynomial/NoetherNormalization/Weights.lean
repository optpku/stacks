module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.MvPolynomial.Basic
public import ReasLib.Data.Finsupp.Weight

@[expose] public section

/-!
# Dominating support weights

This leaf owns the purely combinatorial weight condition on the support of a
finite-variable multivariate polynomial. It is independent of a coordinate
change or a quotient construction.
-/

namespace MvPolynomial.NoetherNormalization

universe u

variable {R : Type u} [CommSemiring R]
variable {n : ℕ}

/-- A choice of weights, normalized to one at the last coordinate, that dominates the pairwise
coordinate spread of the support of a multivariate polynomial. -/
@[stacks 051N "dominating weights for polynomial support"]
def DominatingWeights (g : MvPolynomial (Fin (n + 1)) R) (e : Fin n → ℕ) : Prop :=
  g.support.Nonempty ∧ Finsupp.tailDominates (Finsupp.pairSpread g.support) (Fin.snoc e 1)

namespace DominatingWeights

/-- A dominating weight system has nonempty polynomial support. -/
theorem support_nonempty
    {g : MvPolynomial (Fin (n + 1)) R} {e : Fin n → ℕ}
    (he : DominatingWeights g e) :
    g.support.Nonempty := sorry

/-- Every non-last weight in a dominating system is positive. -/
theorem positive
    {g : MvPolynomial (Fin (n + 1)) R} {e : Fin n → ℕ}
    (he : DominatingWeights g e) (i : Fin n) :
    0 < e i := sorry

/-- A nonempty finite polynomial support admits normalized weights dominating its pairwise
coordinate spread. -/
theorem exists_of_support_nonempty
    (g : MvPolynomial (Fin (n + 1)) R) (hsupport : g.support.Nonempty) :
    ∃ e : Fin n → ℕ, DominatingWeights g e := sorry

/-- A nonzero polynomial admits normalized weights dominating the pairwise spread of its support. -/
theorem exists_of_ne_zero
    (g : MvPolynomial (Fin (n + 1)) R) (hg : g ≠ 0) :
    ∃ e : Fin n → ℕ, DominatingWeights g e := sorry

end DominatingWeights

end MvPolynomial.NoetherNormalization
