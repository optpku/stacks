/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Characterization
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.162.15 (Nagata)

@stack 0334

The neutral ring-level Nagata characterization is owned by
`ReasLib.RingTheory.Normal.Nagata.Characterization`.  This chapter file is a
compatibility entry point for the textbook proposition.
-/

@[stacks 0334]
#check @NagataRing.tfae
#check @NagataRing.iff_universallyJapanese_noetherian
#check @NagataRing.toUniversallyJapanese
