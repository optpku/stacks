/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.FrobeniusGraph
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.MvPolynomial.Variables

@[expose] public section

noncomputable section

namespace MvPolynomial.FrobeniusGraph

/-- The sum of the squares of the four source coordinates. -/
def sumSquares : MvPolynomial Coord ℤ :=
  X .x ^ 2 + X .y ^ 2 + X .u ^ 2 + X .v ^ 2

/-- The first factor in the Frobenius-graph specialization of `sumSquares`. -/
def sumSquaresFactorLeft (p : ℕ) : MvPolynomial (Fin 2) (ZMod p) :=
  X (0 : Fin 2) ^ 2 + X (1 : Fin 2) ^ 2

/-- The second factor in the Frobenius-graph specialization of `sumSquares`. -/
def sumSquaresFactorRight (p : ℕ) : MvPolynomial (Fin 2) (ZMod p) :=
  sumSquaresFactorLeft p ^ (p - 1) + 1

/-- The specialization of `sumSquares` is the product of its two displayed
plane factors for every prime modulus. -/
theorem sumSquares_specialize_eq_mul (p : ℕ) [Fact p.Prime] :
    specialize p sumSquares = sumSquaresFactorLeft p * sumSquaresFactorRight p := sorry

/-- The first displayed factor of `sumSquares` has positive total degree. -/
theorem sumSquaresFactorLeft_totalDegree_pos (p : ℕ) [Fact p.Prime] :
    0 < (sumSquaresFactorLeft p).totalDegree := sorry

/-- The second displayed factor of `sumSquares` has positive total degree. -/
theorem sumSquaresFactorRight_totalDegree_pos (p : ℕ) [Fact p.Prime] :
    0 < (sumSquaresFactorRight p).totalDegree := sorry

/-- The polynomial `sumSquares` uses more than just the source coordinates
`x` and `u`. -/
theorem sumSquares_not_mem_xu : ¬ vars sumSquares ⊆ {.x, .u} := sorry

/-- The polynomial `sumSquares` uses more than just the source coordinates
`y` and `v`. -/
theorem sumSquares_not_mem_yv : ¬ vars sumSquares ⊆ {.y, .v} := sorry

/-- The image of `sumSquares` over the rationals is irreducible. -/
theorem sumSquares_irreducible :
    Irreducible (map (Int.castRingHom ℚ) sumSquares) := sorry

/-- The Frobenius-graph specialization of `sumSquares` has two nonconstant
factors for every prime modulus. -/
theorem sumSquares_specialize_isReducible (p : ℕ) [Fact p.Prime] :
    ∃ g h : MvPolynomial (Fin 2) (ZMod p),
      specialize p sumSquares = g * h ∧ 0 < g.totalDegree ∧ 0 < h.totalDegree := sorry

end MvPolynomial.FrobeniusGraph
