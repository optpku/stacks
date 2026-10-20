/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.FrobeniusGraph.SumSquares
import StacksCheckRecall

#check (MvPolynomial.FrobeniusGraph.sumSquares :
  MvPolynomial MvPolynomial.FrobeniusGraph.Coord ℤ)
#check (MvPolynomial.FrobeniusGraph.sumSquaresFactorLeft :
  ∀ p : ℕ, MvPolynomial (Fin 2) (ZMod p))
#check (MvPolynomial.FrobeniusGraph.sumSquaresFactorRight :
  ∀ p : ℕ, MvPolynomial (Fin 2) (ZMod p))
#check (MvPolynomial.FrobeniusGraph.sumSquares_specialize_eq_mul :
  ∀ (p : ℕ), Fact p.Prime →
    MvPolynomial.FrobeniusGraph.specialize p
        MvPolynomial.FrobeniusGraph.sumSquares =
      MvPolynomial.FrobeniusGraph.sumSquaresFactorLeft p *
        MvPolynomial.FrobeniusGraph.sumSquaresFactorRight p)
#check (MvPolynomial.FrobeniusGraph.sumSquaresFactorLeft_totalDegree_pos :
  ∀ (p : ℕ), Fact p.Prime →
    0 < (MvPolynomial.FrobeniusGraph.sumSquaresFactorLeft p).totalDegree)
#check (MvPolynomial.FrobeniusGraph.sumSquaresFactorRight_totalDegree_pos :
  ∀ (p : ℕ), Fact p.Prime →
    0 < (MvPolynomial.FrobeniusGraph.sumSquaresFactorRight p).totalDegree)
#check (MvPolynomial.FrobeniusGraph.sumSquares_not_mem_xu :
  ¬ MvPolynomial.vars MvPolynomial.FrobeniusGraph.sumSquares ⊆
    {.x, .u})
#check (MvPolynomial.FrobeniusGraph.sumSquares_not_mem_yv :
  ¬ MvPolynomial.vars MvPolynomial.FrobeniusGraph.sumSquares ⊆
    {.y, .v})
#check (MvPolynomial.FrobeniusGraph.sumSquares_irreducible :
  Irreducible (MvPolynomial.map (Int.castRingHom ℚ)
    MvPolynomial.FrobeniusGraph.sumSquares))

/- Exercise 111.29.3 -/
@[stacks 02EQ] #check
  (@MvPolynomial.FrobeniusGraph.sumSquares_specialize_isReducible :
    ∀ (p : ℕ), Fact p.Prime →
      ∃ g h : MvPolynomial (Fin 2) (ZMod p),
        MvPolynomial.FrobeniusGraph.specialize p
            MvPolynomial.FrobeniusGraph.sumSquares = g * h ∧
          0 < g.totalDegree ∧ 0 < h.totalDegree)
