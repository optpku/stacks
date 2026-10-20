/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.HyperbolicQuadric
public import ReasLib.RingTheory.MvPolynomial.Nonisomorphism
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.1.4 (1): over a field `k`, the polynomial rings in `n` and `n + 1`
variables are not isomorphic as `k`-algebras for any `n ≥ 1`. -/
@[stacks 02CJ]
#check (MvPolynomial.not_algEquiv_fin_succ :
  ∀ (k : Type u) [Field k] (n : ℕ),
    1 ≤ n → ¬ Nonempty (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k))

/- Exercise 111.1.4 (2): the quotient `k[a, b, c, d, e, f] / (ab + cd + ef)` is not
isomorphic as a `k`-algebra to the polynomial ring in `n = 5` variables. -/
@[stacks 02CJ]
#check (HyperbolicQuadric.not_algEquiv_mvPolynomial_five :
  ∀ (k : Type u) [Field k],
    ¬ Nonempty (HyperbolicQuadric.CoordinateRing k ≃ₐ[k] MvPolynomial (Fin 5) k))

/- Exercise 111.1.4 (3): the quotient `k[a, b, c, d, e, f] / (ab + cd + ef)` is not
isomorphic as a `k`-algebra to the polynomial ring in `n = 6` variables. -/
@[stacks 02CJ]
#check (HyperbolicQuadric.not_algEquiv_mvPolynomial_six :
  ∀ (k : Type u) [Field k],
    ¬ Nonempty (HyperbolicQuadric.CoordinateRing k ≃ₐ[k] MvPolynomial (Fin 6) k))
