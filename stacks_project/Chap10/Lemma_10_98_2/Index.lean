/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.InverseSystem
import StacksCheckRecall

@[expose] public section

/-!
# Shared Recall for Lemma 10.98.2 Support

This compatibility entrypoint intentionally owns no chapter-local API; clients
should import the shared adic inverse-system leaf directly.

@stack 09B8
-/

@[stacks 09B8 "successive quotient comparison equivalence"]
#check @CategoryTheory.PNatInverseSystem.limitProjectionQuotientEquiv

@[stacks 09B8 "adic completeness of the inverse limit"]
#check @CategoryTheory.PNatInverseSystem.isAdicComplete_limit_of_successiveIdealPowerQuotients
