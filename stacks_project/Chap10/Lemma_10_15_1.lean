/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Operations
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.15.1

@stack 07K1
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.15.1: the textbook implication
`I * J ≤ 𝔭 → I ≤ 𝔭 ∨ J ≤ 𝔭` for a prime ideal `𝔭` is the forward direction of the
canonical theorem `Ideal.IsPrime.mul_le`, which states the equivalent condition
`I * J ≤ 𝔭 ↔ I ≤ 𝔭 ∨ J ≤ 𝔭`. -/
@[stacks 07K1]
#check @Ideal.IsPrime.mul_le
