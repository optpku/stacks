/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.DirectSum
import StacksCheckRecall

/-!
# Flatness of completed free modules

@stack 06LE
-/

@[expose] public section

/- Lemma 15.27.2: over a Noetherian ring, the adic completion of a free module of
arbitrary rank is flat. -/
@[stacks 06LE "Lemma 15.27.2"]
#check @AdicCompletion.directSum_flat
