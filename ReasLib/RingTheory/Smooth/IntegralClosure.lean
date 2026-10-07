module

public import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral representatives in polynomial quotients

@stack 03GD

This leaf specializes the general integral-coefficient derivative theorem to a principal
polynomial quotient while retaining the explicit representative required by the source.
-/

@[expose] public section

open Polynomial

universe u v

namespace Polynomial

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- Lemma 10.147.1: if `f : R[X]` is monic and `h` is integral over `R` in the quotient by the
image of `f`, then `f' * h` has a representative over `B` whose coefficients are integral over
`R`. -/
@[stacks 03GD]
theorem exists_integral_coeff_representative_derivative_mul
    (f : R[X]) (hf : f.Monic)
    (h : B[X] ⧸ Ideal.span {f.map (algebraMap R B)}) (hint : IsIntegral R h) :
    ∃ g : B[X],
      (∀ i : ℕ, IsIntegral R (g.coeff i)) ∧
        Ideal.Quotient.mk (Ideal.span {f.map (algebraMap R B)})
            (derivative (f.map (algebraMap R B))) * h =
          Ideal.Quotient.mk (Ideal.span {f.map (algebraMap R B)}) g := sorry

end Polynomial
