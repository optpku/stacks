module

public import Mathlib.RingTheory.Finiteness.Prod
public import ReasLib.RingTheory.FittingIdeal.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fitting ideals of quotient modules

@stack 0H73

This leaf records the elementary quotient and two-factor product calculations for intrinsic
Fitting ideals.
-/

@[expose] public section

open scoped FittingIdeal

universe u

namespace FittingIdeal

variable {R : Type u} [CommRing R]

/-- The zeroth Fitting ideal of `R ⧸ I` is `I`. -/
@[stacks 0H73 "zeroth Fitting ideal of a quotient"]
theorem quotientAtZero (I : Ideal R) :
    Fit[R]_(0)(R ⧸ I) = I := sorry

/-- The zeroth Fitting ideal of `(R ⧸ I) × (R ⧸ J)` is `I * J`. -/
@[stacks 0H73 "zeroth Fitting ideal of a product of quotients"]
theorem quotientProdAtZero (I J : Ideal R) :
    Fit[R]_(0)((R ⧸ I) × (R ⧸ J)) = I * J := sorry

/-- The first Fitting ideal of `(R ⧸ I) × (R ⧸ J)` is `I + J`. -/
@[stacks 0H73 "first Fitting ideal of a product of quotients"]
theorem quotientProdAtOne (I J : Ideal R) :
    Fit[R]_(1)((R ⧸ I) × (R ⧸ J)) = I + J := sorry

end FittingIdeal
