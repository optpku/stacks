/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.IdempotentLifting.Correction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.32.7

@stack 05BU
-/

/- Lemma 10.32.7 (Tag 05BU): a possibly noncommutative ring element with nilpotent idempotency
defect has an idempotent correction of the form `e + (e ^ 2 - e) * Polynomial.aeval e q`. -/
@[stacks 05BU]
#check @IsNilpotent.exists_polynomial_idempotent_correction

/- The unbundled correction form is the convenient downstream companion of Lemma 10.32.7. -/
@[stacks 05BU]
#check @IsNilpotent.exists_idempotent_correction
