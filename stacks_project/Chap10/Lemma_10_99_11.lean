/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.QuotientPowers.LocalCriterion
import StacksCheckRecall

/-!
# Flatness from flat ideal-power quotients

@stack 0523
-/

@[expose] public section

@[stacks 0523 "(1), prime-local form"]
#check @Module.Flat.QuotientPowers.atPrime

@[stacks 0523 "(2), local-target form"]
#check @Module.Flat.QuotientPowers.of_isLocalRing
