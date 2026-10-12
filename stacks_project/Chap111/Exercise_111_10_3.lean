/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Intersection
public import ReasLib.RingTheory.Ideal.AssociatedPrime.MvPolynomial
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.10.3 (1): for a Noetherian ring `R` and incomparable prime ideals `p`, `q`
(that is, `¬ p ≤ q` and `¬ q ≤ p`), writing `N = R ⧸ (p ⊓ q)`, one has
`associatedPrimesOfModule R N = {p, q}`. -/
@[stacks 0CRA] #check
  (associatedPrimesOfModule.quotient_inf_eq_pair :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p),
      associatedPrimesOfModule R (R ⧸ (p ⊓ q)) = {p, q})

open MvPolynomial

/- Exercise 111.10.3 (2): for a field `k`, writing `R = MvPolynomial (Fin 3) k` with
`X 0` corresponding to `x`, `X 1` corresponding to `y`, and `X 2` corresponding to `z`,
the module `M = R ⧸ (Ideal.span {X 0, X 1} * Ideal.span {X 0, X 2})` can have an associated
prime other than `Ideal.span {X 0, X 1}` or `Ideal.span {X 0, X 2}`; explicitly,
`Ideal.span {X 0, X 1, X 2}` lies in
`associatedPrimesOfModule R M \ {Ideal.span {X 0, X 1}, Ideal.span {X 0, X 2}}`. -/
@[stacks 0CRA] #check
  (MvPolynomial.span_XYZ_mem_associatedPrimesOfModule_quotient_mul_span_XY_XZ :
    ∀ (k : Type u) [Field k],
    Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 1, X 2} ∈
      associatedPrimesOfModule (MvPolynomial (Fin 3) k)
          (MvPolynomial (Fin 3) k ⧸
            (Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 1} *
              Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2})) \
        {Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 1},
          Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2}})
