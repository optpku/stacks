/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Andre
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 15.49.2 (07PM)

@stack 07PM
-/


/- Proposition 15.49.2: regularity, closed-fiber regularity, and the two adic
formal-smoothness conditions are equivalent over a complete local source. -/
@[stacks 07PM "Proposition 15.49.2"]
#check @regularRingMap_specialFiber_formallySmooth_tfae_of_completeLocal

#check @regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion
