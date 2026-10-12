/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open MvPolynomial

namespace MvPolynomial.XyEqSeven

/-- The plane equation `X 0 * X 1 - 7` in `ℤ[x, y]`, with `X 0` corresponding to `x`
and `X 1` corresponding to `y`. -/
def relation : MvPolynomial (Fin 2) ℤ :=
  X 0 * X 1 - 7

/-- The defining equation is `X 0 * X 1 - 7`. -/
theorem relation_eq : relation = X 0 * X 1 - 7 := sorry

/-- The coordinate ring `ℤ[x, y] ⧸ (X 0 * X 1 - 7)`. -/
abbrev CoordinateRing : Type :=
  MvPolynomial (Fin 2) ℤ ⧸ Ideal.span {relation}

/-- The images of `X 0` and `X 1` multiply to `7` in the coordinate ring. -/
theorem mk_X_mul_mk_Y_eq_seven :
    Ideal.Quotient.mk (Ideal.span {relation}) (X 0) *
      Ideal.Quotient.mk (Ideal.span {relation}) (X 1) = 7 := sorry

/-- Exercise 111.58.6: `CoordinateRing`, the quotient `ℤ[x, y] ⧸ (X 0 * X 1 - 7)`, is a
regular ring. -/
@[stacks 0D5L, instance]
instance instIsRegularRing : IsRegularRing CoordinateRing := sorry

end MvPolynomial.XyEqSeven
