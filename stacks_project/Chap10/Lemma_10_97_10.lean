/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Completeness.Quotient
import StacksCheckRecall

@[expose] public section

/-!
@stack 0DYC

# Adic completeness from a complete quotient
-/

/- Lemma 10.97.10: if `A` is `I`-adically complete and `A ⧸ I` is complete for the
adic topology defined by the image of `J`, then `A` is `J`-adically complete. -/
@[stacks 0DYC]
#check @IsAdicComplete.of_quotient
