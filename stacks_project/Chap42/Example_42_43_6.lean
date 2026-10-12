/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton
import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.Evaluation

open AlgebraicGeometry CategoryTheory

universe u

/- Example 42.43.6 (1): the integral Newton polynomial `Pₚ`. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.polynomial : ℕ+ → MvPolynomial ℕ ℤ)

/- Example 42.43.6 (2): `Pₚ` is homogeneous for the grading `deg(cᵢ) = i`. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.polynomial_isWeightedHomogeneous :
    ∀ p : ℕ+, MvPolynomial.IsWeightedHomogeneous Nat.succ
      (AlgebraicGeometry.ChernPolynomial.Newton.polynomial p) p)

/- Example 42.43.6 (3): elementary-symmetric substitution evaluates `Pₚ` to a power sum. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.polynomial_eval :
    ∀ (p : ℕ+) (n : ℕ), (p : ℕ) ≤ n →
      MvPolynomial.aeval (AlgebraicGeometry.ChernPolynomial.Newton.elementaryValue n)
          (AlgebraicGeometry.ChernPolynomial.Newton.polynomial p) =
        MvPolynomial.psum (Fin n) ℤ p)

/- Example 42.43.6 (4): homogeneity and universal evaluation uniquely characterize `Pₚ`. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.eq_polynomial_iff :
    ∀ (p : ℕ+) (Q : MvPolynomial ℕ ℤ),
      Q = AlgebraicGeometry.ChernPolynomial.Newton.polynomial p ↔
        MvPolynomial.IsWeightedHomogeneous Nat.succ Q p ∧
          ∀ n : ℕ, (p : ℕ) ≤ n →
            MvPolynomial.aeval (AlgebraicGeometry.ChernPolynomial.Newton.elementaryValue n) Q =
              MvPolynomial.psum (Fin n) ℤ p)

/- Example 42.43.6 (5): the logarithmic generating-series characterization of `Pₚ`. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.log_chernSeries :
    PowerSeries.logOf AlgebraicGeometry.ChernPolynomial.Newton.chernSeries =
      PowerSeries.mk fun
        | 0 => 0
        | n + 1 =>
            MvPolynomial.C (((-1 : ℚ) ^ n) / (n + 1)) *
              MvPolynomial.map (Int.castRingHom ℚ)
                (AlgebraicGeometry.ChernPolynomial.Newton.polynomial n.succPNat))

/- Example 42.43.6 (6): the integral Newton recurrence. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.augmented_succ :
    ∀ n : ℕ,
      AlgebraicGeometry.ChernPolynomial.Newton.augmented (n + 1) =
        (∑ j ∈ Finset.range n,
          MvPolynomial.C ((-1 : ℤ) ^ j) * MvPolynomial.X (j + 1) *
            AlgebraicGeometry.ChernPolynomial.Newton.augmented (n - j)) +
        MvPolynomial.C ((-1 : ℤ) ^ n * (n + 1 : ℕ)) * MvPolynomial.X (n + 1))

/- Example 42.43.6 (7): the formula `P₁ = c₁`. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.augmented_one :
    AlgebraicGeometry.ChernPolynomial.Newton.augmented 1 = MvPolynomial.X 1)

/- Example 42.43.6 (8): the formula `P₂ = c₁² - 2c₂`. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.augmented_two :
    AlgebraicGeometry.ChernPolynomial.Newton.augmented 2 =
      MvPolynomial.X 1 ^ 2 - 2 * MvPolynomial.X 2)

/- Example 42.43.6 (9): the formula `P₃ = c₁³ - 3c₁c₂ + 3c₃`. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.augmented_three :
    AlgebraicGeometry.ChernPolynomial.Newton.augmented 3 =
      MvPolynomial.X 1 ^ 3 - 3 * MvPolynomial.X 1 * MvPolynomial.X 2 +
        3 * MvPolynomial.X 3)

/- Example 42.43.6 (10): the formula `P₄ = c₁⁴ - 4c₁²c₂ + 4c₁c₃ + 2c₂² - 4c₄`. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.augmented_four :
    AlgebraicGeometry.ChernPolynomial.Newton.augmented 4 =
      MvPolynomial.X 1 ^ 4 - 4 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 +
        4 * MvPolynomial.X 1 * MvPolynomial.X 3 + 2 * MvPolynomial.X 2 ^ 2 -
          4 * MvPolynomial.X 4)

/- Example 42.43.6 (11): intrinsic evaluation of `Pₚ` on a finite locally free module. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.value_spec :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
      (classes : ChernClass.Theory δ f) (E : X.Modules) [E.IsFiniteLocallyFree] (n : ℕ),
      ChernClass.homogeneous δ f n
          (AlgebraicGeometry.ChernPolynomial.Newton.value δ f classes E n) =
        (AlgebraicGeometry.ChernPolynomial.eval δ f classes E
          (AlgebraicGeometry.ChernPolynomial.Newton.augmented n)).1)

/- Example 42.43.6 (12): `P₀(E)` is the rank class. -/
@[stacks 0F9B] #check
  (AlgebraicGeometry.ChernPolynomial.Newton.value_zero :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
      (classes : ChernClass.Theory δ f) (E : X.Modules) [E.IsFiniteLocallyFree],
      ChernClass.homogeneous δ f 0
          (AlgebraicGeometry.ChernPolynomial.Newton.value δ f classes E 0) =
        ChernClass.homogeneous δ f 0 (ChernClass.rankClass δ f E))
