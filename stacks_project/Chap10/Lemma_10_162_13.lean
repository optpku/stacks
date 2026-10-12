/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Nagata
import StacksCheckRecall

@[expose] public section

/-!
# Analytically Unramified Local Nagata Domains
@stack 0331

The source statement is the canonical instance exported by ReasLib.
-/

-- Lemma 10.162.13, tag `0331`: every local Nagata domain is analytically unramified.
@[stacks 0331]
#check @NagataRing.analyticallyUnramified
