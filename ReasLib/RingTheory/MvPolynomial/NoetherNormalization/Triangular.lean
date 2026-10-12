/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.MvPolynomial.Fin
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Weights

@[expose] public section

/-!
# Additive triangular coordinate changes

This leaf records the semiring-level triangular substitution and its
last-variable leading-term API.
-/

open scoped BigOperators
open MvPolynomial

namespace MvPolynomial.NoetherNormalization

universe u

variable {R : Type u} [CommSemiring R]
variable {n : ℕ}

/-- The triangular coordinate map that adds a prescribed power of the last variable to each
non-last coordinate. -/
@[stacks 051N "additive triangular polynomial coordinate map"]
noncomputable def addShear (e : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.aeval
    (Fin.snoc (fun i : Fin n ↦ X i.castSucc + X (Fin.last n) ^ e i) (X (Fin.last n)))

/-- `addShear` sends a non-last coordinate to that coordinate plus the prescribed last-variable
power. -/
@[simp]
theorem addShear_X_castSucc (e : Fin n → ℕ) (i : Fin n) :
    addShear e (X i.castSucc) =
      MvPolynomial.X (R := R) i.castSucc +
        MvPolynomial.X (R := R) (Fin.last n) ^ e i := sorry

/-- `addShear` fixes the last coordinate. -/
@[simp]
theorem addShear_X_last (e : Fin n → ℕ) :
    addShear e (X (Fin.last n)) = MvPolynomial.X (R := R) (Fin.last n) := sorry

/-- View the additive triangular transform of a multivariate polynomial as a polynomial in its
last variable. -/
@[stacks 051N "last-variable polynomial after triangular substitution"]
noncomputable def lastVariablePolynomial (e : Fin n → ℕ)
    (g : MvPolynomial (Fin (n + 1)) R) : Polynomial (MvPolynomial (Fin n) R) :=
  MvPolynomial.Fin.lastVariableEquiv (A := R) n (addShear e g)

/-- The triangularly transformed monomial has the displayed last-variable factorization. -/
theorem lastVariablePolynomial_monomial
    (e : Fin n → ℕ) (m : Fin (n + 1) →₀ ℕ) (r : R) :
    lastVariablePolynomial e (monomial m r) =
      Polynomial.C (MvPolynomial.C r) *
        (Polynomial.X ^ m (Fin.last n) *
          ∏ i : Fin n, (Polynomial.C (X i) + Polynomial.X ^ e i) ^ m i.castSucc) := sorry

/-- The nonconstant factor of a transformed monomial is monic in the last variable. -/
theorem monic_lastVariablePolynomial_monomial_tail
    (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i) (m : Fin (n + 1) →₀ ℕ) :
    (Polynomial.X ^ m (Fin.last n) *
        ∏ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^
          m i.castSucc).Monic := sorry

/-- The monic factor of a transformed monomial has degree equal to its normalized weight. -/
theorem natDegree_lastVariablePolynomial_monomial_tail
    [Nontrivial R] (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i) (m : Fin (n + 1) →₀ ℕ) :
    (Polynomial.X ^ m (Fin.last n) *
        ∏ i : Fin n, (Polynomial.C (MvPolynomial.X (R := R) i) + Polynomial.X ^ e i) ^
          m i.castSucc).natDegree =
      m.weight (Fin.snoc e 1) := sorry

/-- A transformed nonzero monomial has degree equal to its normalized weight. -/
theorem natDegree_lastVariablePolynomial_monomial
    [Nontrivial R] (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i)
    (m : Fin (n + 1) →₀ ℕ) {r : R} (hr : r ≠ 0) :
    (lastVariablePolynomial e (monomial m r)).natDegree = m.weight (Fin.snoc e 1) := sorry

/-- The top last-variable coefficient of a transformed monomial is its original scalar
coefficient. -/
theorem leadingCoeff_lastVariablePolynomial_monomial
    (e : Fin n → ℕ) (he_pos : ∀ i : Fin n, 0 < e i) (m : Fin (n + 1) →₀ ℕ) {r : R} :
    (lastVariablePolynomial e (monomial m r)).leadingCoeff = C r := sorry

/-- Lemma 10.115.2, tag 051N: after an additive triangular substitution with dominating weights,
a nonconstant polynomial has positive last-variable degree and a constant leading coefficient
taken from its original support. -/
@[stacks 051N]
theorem exists_positive_natDegree_and_constant_leadingCoeff
    (g : MvPolynomial (Fin (n + 1)) R) (hg : ¬ ∃ a : R, g = C a)
    (e : Fin n → ℕ) (he : DominatingWeights g e) :
    let p := lastVariablePolynomial e g
    0 < p.natDegree ∧ ∃ a : R, p.leadingCoeff = C a ∧ ∃ m ∈ g.support, g.coeff m = a := sorry

end MvPolynomial.NoetherNormalization
