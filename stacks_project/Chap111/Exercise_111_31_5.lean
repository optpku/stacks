/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.RegularFunctions
public import ReasLib.AlgebraicGeometry.AffineLine.RegularFunctions
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.31.5 (1): over an algebraically closed field, regular functions on affine
space are polynomial. -/
@[stacks 078W] #check (MvPolynomial.isPolynomial_of_isRegular_univ :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (φ : ∀ (x : (Set.univ : Set (Fin n → k))), k),
    MvPolynomial.IsRegular φ → MvPolynomial.IsPolynomial φ)

/- Exercise 111.31.5 (2): every function on a Zariski locally closed affine subset over a
finite field is regular. -/
@[stacks 078W] #check (MvPolynomial.isRegular_of_finite :
  ∀ {k : Type u} [Field k] [Finite k] {n : ℕ} {Z : Set (Fin n → k)},
    MvPolynomial.IsZariskiLocallyClosed Z → ∀ (φ : Z → k), MvPolynomial.IsRegular φ)

/- Exercise 111.31.5 (3): the algebra of regular functions on a Zariski locally closed affine
subset over a finite field is finite-dimensional. -/
@[stacks 078W] #check (MvPolynomial.finiteDimensional_regularFunctions :
  ∀ {k : Type u} [Field k] [Finite k] {n : ℕ} {Z : Set (Fin n → k)},
    MvPolynomial.IsZariskiLocallyClosed Z →
      FiniteDimensional k (MvPolynomial.regularFunctions Z))

/- Exercise 111.31.5 (4): the reciprocal of `1 + x ^ 2` is regular on the real line but is
not polynomial. -/
@[stacks 078W] #check (Polynomial.isRegular_not_isPolynomial_invOneAddSq :
  Polynomial.IsRegular (fun z : (Set.univ : Set ℝ) ↦ Polynomial.invOneAddSq z.val) ∧
    ¬ Polynomial.IsPolynomial (fun z : (Set.univ : Set ℝ) ↦ Polynomial.invOneAddSq z.val))

/- Exercise 111.31.5 (5): the reciprocal of `x ^ 2 - p` is regular on the p-adic line but is
not polynomial. -/
@[stacks 078W] #check (Polynomial.isRegular_not_isPolynomial_invXSqSubNat :
  ∀ (p : ℕ) [Fact p.Prime],
    Polynomial.IsRegular (fun z : (Set.univ : Set ℚ_[p]) ↦ Polynomial.invXSqSubNat p z.val) ∧
      ¬ Polynomial.IsPolynomial
        (fun z : (Set.univ : Set ℚ_[p]) ↦ Polynomial.invXSqSubNat p z.val))
