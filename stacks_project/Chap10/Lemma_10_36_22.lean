/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.GoingUp
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.36.22

@stack 00GU

Going up for prime ideals in an integral extension is exactly the canonical Mathlib theorem below.
-/

/- Lemma 10.36.22: let `R → S` be integral, let `p ⊆ p'` be prime ideals of `R`, and let
`Q` be a prime ideal of `S` lying over `p`. Then there is a prime `Q'` of `S` with `Q ⊆ Q'`
lying over `p'`. -/
@[stacks 00GU "going up for integral extensions"]
#check @Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
