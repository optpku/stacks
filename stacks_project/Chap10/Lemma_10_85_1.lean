/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Finiteness.Projective.CountablyGenerated
import StacksCheckRecall

/-!
# Lemma 10.85.1

@stack 0590
-/

@[expose] public section

/- Lemma 10.85.1: every projective `R`-module is free if and only if every
countably generated projective `R`-module is free. -/
@[stacks 0590]
#check @Module.Projective.all_free_iff_all_countablyGenerated_free
