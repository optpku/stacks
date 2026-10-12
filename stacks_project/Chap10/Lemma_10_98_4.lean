/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Graded
import StacksCheckRecall

/-!
# Lemma 10.98.4

@stack 0EKD
-/

@[expose] public section

/- Lemma 10.98.4 (0EKD): an isomorphism from the completed tensor product to
the limit of a degree-preserving positive inverse system induces an isomorphism
on every homogeneous degree.  The cone-based statement avoids a separate raw
compatible-family presentation and uses the canonical degree-zero scalar
restriction. -/
@[stacks 0EKD]
#check @AdicCompletion.Graded.degreewiseLimitMap_isIso

#check @GradedModule.PNat.degreewise
#check @GradedModule.PNat.limitMap
