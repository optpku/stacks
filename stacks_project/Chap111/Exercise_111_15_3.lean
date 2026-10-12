/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.PseudoDivision
import StacksCheckRecall

@[expose]
public section

universe u

open Polynomial

/- Exercise 111.15.3: for a commutative ring `R` and `f, g : R[X]` with
`f.natDegree ≤ d`, there exist `N : ℕ` and `q, r : R[X]` such that
`C (f.coeff d) ^ N * g = q * f + r` and `r.degree < d`. -/
@[stacks 0FJ6] #check (Polynomial.exists_C_pow_mul_eq_mul_add_of_natDegree_le :
  ∀ {R : Type u} [CommRing R] (f : R[X]) (d : ℕ)
    (hf : f.natDegree ≤ d) (g : R[X]),
    ∃ (N : ℕ) (q r : R[X]),
      C (f.coeff d) ^ N * g = q * f + r ∧ r.degree < d)

/- After scaling by a power of `C (f.coeff d)`, the remainder may be taken
with vanishing coefficients in degrees at least `d`. -/
#check (Polynomial.exists_C_pow_mul_eq_mul_add_of_natDegree_le_coeff :
  ∀ {R : Type u} [CommRing R] (f : R[X]) (d : ℕ)
    (hf : f.natDegree ≤ d) (g : R[X]),
    ∃ (N : ℕ) (q r : R[X]),
      C (f.coeff d) ^ N * g = q * f + r ∧ ∀ n, d ≤ n → r.coeff n = 0)

/- Scaling by a power of the leading coefficient yields a remainder of
degree strictly less than `f.natDegree`. -/
#check (Polynomial.exists_C_leadingCoeff_pow_mul_eq_mul_add :
  ∀ {R : Type u} [CommRing R] (f g : R[X]),
    ∃ (N : ℕ) (q r : R[X]),
      C (f.leadingCoeff) ^ N * g = q * f + r ∧ r.degree < f.natDegree)
