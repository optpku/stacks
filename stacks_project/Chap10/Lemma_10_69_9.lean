/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.QuasiRegular.Adic

@[expose] public section

/-!
# Lemma 10.69.9

@stack 065N
-/

/- Lemma 10.69.9, tag `065N`: the adic separated-quotient invariance of
quasi-regularity is owned by the shared sequence API. -/
@[stacks 065N "quasi-regularity and adic separated quotients"]
#check @RingTheory.Sequence.IsQuasiRegular.adicSeparatedQuotient_iff
