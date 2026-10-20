module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.147.3

@stack 03GF

The explicit cyclotomic quotient model is retained on the source-facing
statement.  The intermediate root and derivative calculations are proof-only
and are not part of the public API.
-/

noncomputable section

open scoped BigOperators
open Polynomial

section

variable (p d : ℕ)

local notation "K" => Localization.Away (p : ℤ)
local notation "P" => cyclotomic p K
local notation "A" => AdjoinRoot P
local notation "ζ" => (AdjoinRoot.root P : A)

/-- Example 10.147.3: for `d < p`, the first `d` powers of the distinguished root in
`ℤ[1/p][X] / (1 + X + ··· + X^(p - 1))` have unit pairwise-difference product. -/
@[stacks 03GF]
theorem cyclotomic_prime_example_unit_pairwise_difference_product
    [Fact p.Prime] (hd : d < p) :
    IsUnit
      (∏ ij ∈ (Finset.univ : Finset (Fin d)).offDiag with ij.1 < ij.2,
        (ζ ^ (ij.1 : ℕ) - ζ ^ (ij.2 : ℕ))) := sorry

end

@[stacks 03GF "cyclotomic polynomial owner"]
#check @Polynomial.cyclotomic_prime_mul_X_sub_one

@[stacks 03GF "adjoined-root owner"]
#check @AdjoinRoot.root

@[stacks 03GF "source-facing unit product"]
#check @cyclotomic_prime_example_unit_pairwise_difference_product
