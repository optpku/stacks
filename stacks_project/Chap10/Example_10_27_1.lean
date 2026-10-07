module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import StacksCheckRecall

/-!
# The spectrum of `Z[X] / (X^2 - 4)`

@stack 00EY
-/

@[expose] public section

open Polynomial PrimeSpectrum

noncomputable section

/-- The defining ideal `(X^2 - 4)` from Example 10.27.1. -/
def splitQuadraticIdeal : Ideal ℤ[X] :=
  Ideal.span ({X ^ 2 - C (4 : ℤ)} : Set ℤ[X])

/-- The ring `Z[X] / (X^2 - 4)` from Example 10.27.1. -/
abbrev splitQuadraticRing := ℤ[X] ⧸ splitQuadraticIdeal

/-- The class of `X` in `splitQuadraticRing`. -/
def splitQuadraticClass : splitQuadraticRing :=
  (Ideal.Quotient.mk splitQuadraticIdeal) X

/-- **Example 10.27.1** ([Stacks tag 00EY](https://stacks.math.columbia.edu/tag/00EY)):
the points of `Spec(Z[X] / (X^2 - 4))` are exactly `(2, x)`, `(x - 2)`, `(x + 2)`,
or, for a prime `q > 2`, one of `(q, x - 2)` and `(q, x + 2)`. -/
@[stacks 00EY]
theorem prime_spectrum_Zx_mod_xsq_sub_four_cases
    (p : PrimeSpectrum splitQuadraticRing) :
    p.asIdeal =
        Ideal.span ({(2 : splitQuadraticRing), splitQuadraticClass} :
          Set splitQuadraticRing) ∨
      p.asIdeal =
          Ideal.span ({splitQuadraticClass - 2} : Set splitQuadraticRing) ∨
        p.asIdeal =
            Ideal.span ({splitQuadraticClass + 2} : Set splitQuadraticRing) ∨
          ∃ q : ℕ,
            q.Prime ∧ 2 < q ∧
              (p.asIdeal =
                  Ideal.span
                    ({(q : splitQuadraticRing), splitQuadraticClass - 2} :
                      Set splitQuadraticRing) ∨
                p.asIdeal =
                  Ideal.span
                    ({(q : splitQuadraticRing), splitQuadraticClass + 2} :
                      Set splitQuadraticRing)) := sorry

/-- Ideal-level reformulation of Example 10.27.1. -/
@[stacks 00EY "ideal-level classification"]
theorem prime_ideal_Zx_mod_xsq_sub_four_cases (I : Ideal splitQuadraticRing) :
    I.IsPrime ↔
      I =
          Ideal.span ({(2 : splitQuadraticRing), splitQuadraticClass} :
            Set splitQuadraticRing) ∨
        I = Ideal.span ({splitQuadraticClass - 2} : Set splitQuadraticRing) ∨
          I = Ideal.span ({splitQuadraticClass + 2} : Set splitQuadraticRing) ∨
            ∃ q : ℕ,
              q.Prime ∧ 2 < q ∧
                (I =
                    Ideal.span
                      ({(q : splitQuadraticRing), splitQuadraticClass - 2} :
                        Set splitQuadraticRing) ∨
                  I =
                    Ideal.span
                      ({(q : splitQuadraticRing), splitQuadraticClass + 2} :
                        Set splitQuadraticRing)) := sorry

@[stacks 00EY "canonical point object"]
#check @PrimeSpectrum

@[stacks 00EY "prime-ideal view"]
#check @Ideal.IsPrime
