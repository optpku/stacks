/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Excellent.Nagata
import StacksCheckRecall

/-!
# Lemma 15.52.5

@stack 07QV
-/

@[expose] public section

/- Lemma 15.52.5, tag `07QV`: every quasi-excellent ring is Nagata. -/
@[stacks 07QV]
#check @IsQuasiExcellentRing.nagataRing

/- The common same-universe case is registered as a canonical instance. -/
#check @IsQuasiExcellentRing.toNagataRing
