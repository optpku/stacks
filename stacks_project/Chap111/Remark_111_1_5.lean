/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.MvPolynomial.Nonisomorphism
public import ReasLib.RingTheory.MvPolynomial.HyperbolicQuadric

@[expose] public section

universe u

/- Remark 111.1.5: pedagogical guidance for the preceding k-algebra non-isomorphism
exercise, not a new theorem. The idea is to find a simple argument in each case rather
than applying a "big" theorem; nonetheless it is good to be guided by general principles.
The three cases are already recorded as `not_algEquiv_fin_succ`,
`not_algEquiv_mvPolynomial_five`, and `not_algEquiv_mvPolynomial_six`.
Case (1): polynomial rings in n and n + 1 variables, n ≥ 1. -/
@[stacks 02CK]
#check (MvPolynomial.not_algEquiv_fin_succ :
  ∀ (k : Type u) [Field k] (n : ℕ),
    1 ≤ n → ¬ Nonempty (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k))

-- Case (2): hyperbolic quadric coordinate ring versus five variables.
@[stacks 02CK]
#check (HyperbolicQuadric.not_algEquiv_mvPolynomial_five :
  ∀ (k : Type u) [Field k],
    ¬ Nonempty (HyperbolicQuadric.CoordinateRing k ≃ₐ[k] MvPolynomial (Fin 5) k))

-- Case (3): hyperbolic quadric coordinate ring versus six variables.
@[stacks 02CK]
#check (HyperbolicQuadric.not_algEquiv_mvPolynomial_six :
  ∀ (k : Type u) [Field k],
    ¬ Nonempty (HyperbolicQuadric.CoordinateRing k ≃ₐ[k] MvPolynomial (Fin 6) k))
