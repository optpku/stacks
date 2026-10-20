/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.StandardLine
import StacksCheckRecall

universe u

/- Exercise 111.45.3: In projective space of dimension at least one over a field,
the restriction of the degree -102 twisting sheaf to the standard coordinate line,
pushed forward to the ambient space, is coherent and has Hilbert polynomial t - 101. -/
@[stacks 0DCG] #check
  (AlgebraicGeometry.ProjectiveSpace.StandardLine.hilbertPolynomial_twistPushforward_neg102 :
    ∀ (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n),
      AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial k n
        (AlgebraicGeometry.ProjectiveSpace.StandardLine.twistPushforward k n hn (-102)) =
          fun t ↦ t - 101)

#check
  (AlgebraicGeometry.ProjectiveSpace.StandardLine.isHilbertPolynomial_twistPushforward_neg102 :
    ∀ (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n),
      AlgebraicGeometry.ProjectiveSpace.IsHilbertPolynomial k n
        (AlgebraicGeometry.ProjectiveSpace.StandardLine.twistPushforward k n hn (-102))
        (Polynomial.X - Polynomial.C (101 : ℚ)))
