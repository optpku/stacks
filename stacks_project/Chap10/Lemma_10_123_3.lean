/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.ZariskisMainTheorem
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.123.3

@stack 00PV
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.123.3: for an `R`-algebra `S`, if `φ : R[X] →ₐ[R] S`, `t : S` is integral over
`R[X]`, and `φ p * t` lies in the image of `φ`, then after multiplying `t` by a power of
`p.leadingCoeff`, one can subtract `φ q` for some `q : R[X]` and obtain an element integral over
`R`. This is exactly the canonical mathlib theorem
`exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range`. -/
@[stacks 00PV]
#check @exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
