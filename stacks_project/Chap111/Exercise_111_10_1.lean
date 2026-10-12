/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Computations
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

section

open MvPolynomial

/- Exercise 111.10.1 (1): for a field `k`, writing `R = MvPolynomial (Fin 2) k` with
`X 0` corresponding to `x` and `X 1` corresponding to `y`,
`associatedPrimesOfModule R (R ⧸ Ideal.span {X 0 * X 1 * (X 0 + X 1)})` equals
`{Ideal.span {X 0}, Ideal.span {X 1}, Ideal.span {X 0 + X 1}}`. -/
@[stacks 0CR8] #check
  (MvPolynomial.associatedPrimesOfModule_quotient_span_XY_X_add_Y :
    ∀ (k : Type u) [Field k],
    associatedPrimesOfModule (MvPolynomial (Fin 2) k)
        (MvPolynomial (Fin 2) k ⧸
          Ideal.span {(X 0 * X 1 * (X 0 + X 1) : MvPolynomial (Fin 2) k)}) =
      {Ideal.span {X 0}, Ideal.span {X 1}, Ideal.span {X 0 + X 1}})

end

section

open Polynomial

/- Exercise 111.10.1 (2): writing `R = Polynomial ℤ`,
`associatedPrimesOfModule R (R ⧸ Ideal.span {300 * X + 75})` equals
`{Ideal.span {(3 : Polynomial ℤ)}, Ideal.span {(5 : Polynomial ℤ)},
Ideal.span {4 * X + 1}}`. -/
@[stacks 0CR8] #check
  (Polynomial.associatedPrimesOfModule_quotient_span_300X_add_75 :
    associatedPrimesOfModule (Polynomial ℤ)
        (Polynomial ℤ ⧸ Ideal.span {(300 * X + 75 : Polynomial ℤ)}) =
      {Ideal.span {(3 : Polynomial ℤ)}, Ideal.span {(5 : Polynomial ℤ)},
        Ideal.span {4 * X + 1}})

end

section

open MvPolynomial

/- Exercise 111.10.1 (3): for a field `k`, writing `R = MvPolynomial (Fin 3) k` with
`X 0` corresponding to `x`, `X 1` corresponding to `y`, and `X 2` corresponding to `z`,
`associatedPrimesOfModule R (R ⧸ Ideal.span {X 0 ^ 3, X 0 ^ 2 * X 1, X 0 * X 2})` equals
`{Ideal.span {X 0}, Ideal.span {X 0, X 2}, Ideal.span {X 0, X 1, X 2}}`. -/
@[stacks 0CR8] #check
  (MvPolynomial.associatedPrimesOfModule_quotient_span_X_pow_3_X_pow_2_Y_XZ :
    ∀ (k : Type u) [Field k],
    associatedPrimesOfModule (MvPolynomial (Fin 3) k)
        (MvPolynomial (Fin 3) k ⧸
          Ideal.span
            {(X 0 ^ 3 : MvPolynomial (Fin 3) k), X 0 ^ 2 * X 1, X 0 * X 2}) =
      {Ideal.span {X 0}, Ideal.span {X 0, X 2}, Ideal.span {X 0, X 1, X 2}})

end
