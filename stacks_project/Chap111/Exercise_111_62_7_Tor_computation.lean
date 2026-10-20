module

public import ReasLib.RingTheory.MvPolynomial.Tor
import StacksCheckRecall
public import Mathlib.Data.Complex.Basic

@[expose] public section

open MvPolynomial CategoryTheory CategoryTheory.Limits
open scoped ModuleTor

/- Exercise 111.62.7 (Tor computation)
For `R = ℂ[x,y,z]`, `M = R/(x,z)`, and `N = R/(y,z)`, the nonzero integer
Tor degrees are exactly `0` and `1`. The existential nonnegative degree below
expresses the convention that Tor is extended by zero in negative degrees.
-/
@[stacks 0FWR] #check (MvPolynomial.tor_quotient_span_XZ_YZ_not_isZero_int_iff :
  ∀ i : ℤ,
    (∃ n : ℕ, i = n ∧
      ¬ IsZero
        (Tor⁽n⁾[MvPolynomial (Fin 3) ℂ](MvPolynomial (Fin 3) ℂ ⧸
          Ideal.span {(X 0 : MvPolynomial (Fin 3) ℂ), X 2},
          MvPolynomial (Fin 3) ℂ ⧸
            Ideal.span {(X 1 : MvPolynomial (Fin 3) ℂ), X 2}))) ↔
      i = 0 ∨ i = 1)
