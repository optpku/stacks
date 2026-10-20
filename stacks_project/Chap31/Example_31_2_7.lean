/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints.SquareZero

@[expose] public section

universe u

variable (k : Type u) [Field k]

/- The countably generated square-zero polynomial quotient is a local ring. -/
#check (MvPolynomial.SquareZero.quotient_isLocalRing (σ := ℕ) (k := k) :
  IsLocalRing (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)))

/- The maximal ideal of the countably generated square-zero quotient is locally nilpotent. -/
#check (MvPolynomial.SquareZero.maximalIdeal_isLocallyNilpotent (σ := ℕ) (k := k) :
  (IsLocalRing.maximalIdeal
    (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k))).IsLocallyNilpotent)

/- No element of the quotient has annihilator equal to its maximal ideal. -/
#check (MvPolynomial.SquareZero.not_exists_torsionOf_eq_maximalIdeal (σ := ℕ) (k := k) :
  ¬ ∃ x : MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k),
    Ideal.torsionOf
      (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k))
      (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)) x =
        IsLocalRing.maximalIdeal
          (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)))

/- Its exact-annihilator associated-prime set is empty. -/
#check (MvPolynomial.SquareZero.associatedPrimesOfModule_self_eq_empty
    (σ := ℕ) (k := k) :
  associatedPrimesOfModule
    (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k))
    (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)) = ∅)

/- Example 31.2.7: the affine spectrum of the countably generated square-zero polynomial
quotient over a field has no associated points. -/
@[stacks 05AI] #check (MvPolynomial.SquareZero.spec_associatedPoints_eq_empty
    (σ := ℕ) (k := k) :
  AlgebraicGeometry.Scheme.associatedPoints
    (AlgebraicGeometry.Scheme.Spec.obj
      (Opposite.op <| CommRingCat.of
        (MvPolynomial.SquareZero.Quotient (σ := ℕ) (k := k)))) = ∅)
