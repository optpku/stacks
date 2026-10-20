/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

noncomputable section

universe u

open MvPolynomial

/-- The ideal `(X i ^ p)` in `R[x_1, …, x_6]`, indexed by `i : Fin 6`. -/
def MvPolynomial.finSixPPowerIdeal (R : Type u) [CommRing R] (p : ℕ) :
    Ideal (MvPolynomial (Fin 6) R) :=
  Ideal.span (Set.range fun i : Fin 6 ↦ X i ^ p)

/-- Each generator `X i ^ p` lies in `finSixPPowerIdeal R p`. -/
theorem MvPolynomial.X_pow_mem_finSixPPowerIdeal (R : Type u) [CommRing R] (p : ℕ)
    (i : Fin 6) :
    X i ^ p ∈ finSixPPowerIdeal R p := sorry

/-- The truncated polynomial algebra `R[x_1, …, x_6] / (x_1^p, …, x_6^p)`. -/
abbrev MvPolynomial.truncatedPowerAlgebra (R : Type u) [CommRing R] (p : ℕ) : Type u :=
  MvPolynomial (Fin 6) R ⧸ finSixPPowerIdeal R p

/-- The images of the variables in `truncatedPowerAlgebra R p` have `p`-th power zero. -/
theorem MvPolynomial.truncatedPowerAlgebra_X_pow_eq_zero (R : Type u) [CommRing R] (p : ℕ)
    (i : Fin 6) :
    (Ideal.Quotient.mk (finSixPPowerIdeal R p) (X i)) ^ p = 0 := sorry

/-- The special fibre of a `ZMod (p ^ 2)`-algebra, obtained by quotienting by the image of `p`. -/
abbrev zmodSqSpecialFiber (p : ℕ) (B : Type u) [CommRing B] [Algebra (ZMod (p ^ 2)) B] :
    Type u :=
  B ⧸ Ideal.span {algebraMap (ZMod (p ^ 2)) B (p : ZMod (p ^ 2))}

/-- For prime `p`, the six-variable quotient by the `p`-th powers over `ZMod (p ^ 2)`
is flat over `ZMod (p ^ 2)`, and its special fibre is the corresponding quotient over `ZMod p`. -/
theorem MvPolynomial.truncatedPowerAlgebra_zmodSq_flat_specialFiber (p : ℕ) [Fact p.Prime] :
    (algebraMap (ZMod (p ^ 2)) (truncatedPowerAlgebra (ZMod (p ^ 2)) p)).Flat ∧
      Nonempty
        (zmodSqSpecialFiber p (truncatedPowerAlgebra (ZMod (p ^ 2)) p) ≃+*
          truncatedPowerAlgebra (ZMod p) p) := sorry

/-- The hyperbolic quadratic form `x_1 x_2 + x_3 x_4 + x_5 x_6` in six variables. -/
def MvPolynomial.hyperbolicForm (R : Type u) [CommRing R] : MvPolynomial (Fin 6) R :=
  X 0 * X 1 + X 2 * X 3 + X 4 * X 5

/-- The ideal `(x_1^2, …, x_6^2, x_1 x_2 + x_3 x_4 + x_5 x_6)` in `R[x_1, …, x_6]`. -/
def MvPolynomial.hyperbolicTruncatedIdeal (R : Type u) [CommRing R] :
    Ideal (MvPolynomial (Fin 6) R) :=
  finSixPPowerIdeal R 2 ⊔ Ideal.span {hyperbolicForm R}

/-- The algebra `R[x_1, …, x_6] / (x_1^2, …, x_6^2, x_1 x_2 + x_3 x_4 + x_5 x_6)`. -/
abbrev MvPolynomial.hyperbolicTruncatedAlgebra (R : Type u) [CommRing R] : Type u :=
  MvPolynomial (Fin 6) R ⧸ hyperbolicTruncatedIdeal R

/-- The images of the variables in `hyperbolicTruncatedAlgebra R` square to zero. -/
theorem MvPolynomial.hyperbolicTruncatedAlgebra_X_pow_two_eq_zero (R : Type u) [CommRing R]
    (i : Fin 6) :
    (Ideal.Quotient.mk (hyperbolicTruncatedIdeal R) (X i)) ^ 2 = 0 := sorry

/-- The hyperbolic quadratic form vanishes in `hyperbolicTruncatedAlgebra R`. -/
theorem MvPolynomial.hyperbolicTruncatedAlgebra_hyperbolicForm_eq_zero (R : Type u)
    [CommRing R] :
    Ideal.Quotient.mk (hyperbolicTruncatedIdeal R) (hyperbolicForm R) = 0 := sorry

/-- No flat `ZMod 4`-algebra has special fibre isomorphic to the six-variable
square-zero quotient over `ZMod 2` with the hyperbolic quadratic relation. -/
theorem MvPolynomial.not_exists_flat_zmodFour_algebra (B : Type u) [CommRing B]
    [Algebra (ZMod 4) B] :
    ¬((algebraMap (ZMod 4) B).Flat ∧
        Nonempty (zmodSqSpecialFiber 2 B ≃+* hyperbolicTruncatedAlgebra (ZMod 2))) := sorry
