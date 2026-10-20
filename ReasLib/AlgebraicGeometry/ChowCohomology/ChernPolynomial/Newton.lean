module

public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.PowerSeries.Log

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.ChernPolynomial.Newton

/-- The integral Newton polynomial in variables indexed by positive degree, obtained by
expressing a power sum in the elementary symmetric polynomials. -/
noncomputable def polynomial (p : ℕ+) : MvPolynomial ℕ ℤ :=
  MvPolynomial.rename (fun i : Fin (p : ℕ) ↦ (i : ℕ))
    ((MvPolynomial.esymmAlgEquiv (Fin (p : ℕ)) ℤ (Fintype.card_fin _)).symm
      ⟨MvPolynomial.psum (Fin (p : ℕ)) ℤ p,
        MvPolynomial.psum_isSymmetric (Fin (p : ℕ)) ℤ p⟩)

/-- The elementary-symmetric specialization in `n` root variables, with index `i`
standing for the Chern variable `cᵢ₊₁`. -/
def elementaryValue (n : ℕ) (i : ℕ) : MvPolynomial (Fin n) ℤ :=
  MvPolynomial.esymm (Fin n) ℤ (i + 1)

/-- The elementary specialization sends index `i` to the elementary symmetric
polynomial of degree `i + 1`. -/
theorem elementaryValue_apply (n i : ℕ) :
    elementaryValue n i = MvPolynomial.esymm (Fin n) ℤ (i + 1) := sorry

/-- The Newton polynomial of positive degree `p` is homogeneous of weighted degree `p`
when variable `i` has weight `i + 1`. -/
theorem polynomial_isWeightedHomogeneous (p : ℕ+) :
    MvPolynomial.IsWeightedHomogeneous Nat.succ (polynomial p) p := sorry

/-- Substitution of elementary symmetric polynomials in at least `p` roots evaluates
the Newton polynomial to the `p`th power sum. -/
theorem polynomial_eval (p : ℕ+) (n : ℕ) (hpn : (p : ℕ) ≤ n) :
    MvPolynomial.aeval (elementaryValue n) (polynomial p) =
      MvPolynomial.psum (Fin n) ℤ p := sorry

/-- Weighted homogeneity and all sufficiently large elementary-symmetric evaluations
characterize the integral Newton polynomial uniquely. -/
theorem eq_polynomial_iff (p : ℕ+) (Q : MvPolynomial ℕ ℤ) :
    Q = polynomial p ↔
      MvPolynomial.IsWeightedHomogeneous Nat.succ Q p ∧
        ∀ n : ℕ, (p : ℕ) ≤ n →
          MvPolynomial.aeval (elementaryValue n) Q = MvPolynomial.psum (Fin n) ℤ p := sorry

/-- The augmented Newton family in variables `r, c₁, c₂, …`; degree zero is the rank
variable and positive degrees are obtained by shifting the variables of `polynomial`. -/
noncomputable def augmented : ℕ → MvPolynomial ℕ ℤ
  | 0 => MvPolynomial.X 0
  | n + 1 => MvPolynomial.rename Nat.succ (polynomial n.succPNat)

/-- The degree-zero augmented Newton polynomial is the rank variable. -/
theorem augmented_zero : augmented 0 = MvPolynomial.X 0 := sorry

/-- The augmented Newton polynomial is homogeneous of its index when variable `i` has
weight `i`. -/
theorem augmented_isWeightedHomogeneous (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous id (augmented n) n := sorry

/-- The augmented Newton family satisfies the integral Newton recurrence. -/
theorem augmented_succ (n : ℕ) :
    augmented (n + 1) =
      (∑ j ∈ Finset.range n,
        MvPolynomial.C ((-1 : ℤ) ^ j) * MvPolynomial.X (j + 1) * augmented (n - j)) +
      MvPolynomial.C ((-1 : ℤ) ^ n * (n + 1 : ℕ)) * MvPolynomial.X (n + 1) := sorry

/-- The formal Chern series `1 + c₁T + c₂T² + ⋯` over rational Chern polynomials. -/
def chernSeries : PowerSeries (MvPolynomial ℕ ℚ) :=
  PowerSeries.mk fun
    | 0 => 1
    | n + 1 => MvPolynomial.X n

/-- The coefficients of the formal Chern series are `1` in degree zero and `cₙ₊₁`
in degree `n + 1`. -/
theorem coeff_chernSeries (n : ℕ) :
    PowerSeries.coeff n chernSeries =
      match n with
      | 0 => 1
      | k + 1 => MvPolynomial.X k := sorry

/-- The formal logarithm of the Chern series has coefficient
`(-1)^(p-1) Pₚ / p` in every positive degree. -/
theorem log_chernSeries :
    PowerSeries.logOf chernSeries =
      PowerSeries.mk fun
        | 0 => 0
        | n + 1 =>
            MvPolynomial.C (((-1 : ℚ) ^ n) / (n + 1)) *
              MvPolynomial.map (Int.castRingHom ℚ) (polynomial n.succPNat) := sorry

/-- The first augmented Newton polynomial is `c₁`. -/
theorem augmented_one : augmented 1 = MvPolynomial.X 1 := sorry

/-- The second augmented Newton polynomial is `c₁² - 2c₂`. -/
theorem augmented_two :
    augmented 2 = MvPolynomial.X 1 ^ 2 - 2 * MvPolynomial.X 2 := sorry

/-- The third augmented Newton polynomial is `c₁³ - 3c₁c₂ + 3c₃`. -/
theorem augmented_three :
    augmented 3 =
      MvPolynomial.X 1 ^ 3 - 3 * MvPolynomial.X 1 * MvPolynomial.X 2 +
        3 * MvPolynomial.X 3 := sorry

/-- The fourth augmented Newton polynomial is
`c₁⁴ - 4c₁²c₂ + 4c₁c₃ + 2c₂² - 4c₄`. -/
theorem augmented_four :
    augmented 4 =
      MvPolynomial.X 1 ^ 4 - 4 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 +
        4 * MvPolynomial.X 1 * MvPolynomial.X 3 + 2 * MvPolynomial.X 2 ^ 2 -
          4 * MvPolynomial.X 4 := sorry

end AlgebraicGeometry.ChernPolynomial.Newton
