/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Flat
import StacksCheckRecall

/-!
# Noetherianity and flatness of adic completions

The Noetherianity clause is the existing completion owner; the module-flatness clause is the
first-Tor criterion owned by the dedicated ReasLib leaf.

@stack 0AGW
-/

@[expose] public section

/- Lemma 15.27.5 (1): the completion is Noetherian. -/
@[stacks 0AGW "Lemma 15.27.5 (1)"]
#check @AdicCompletion.isNoetherianRing

/- Lemma 15.27.5 (2): quotient flatness and vanishing of first Tor imply flatness of the
completed module over the completed ring. -/
@[stacks 0AGW "Lemma 15.27.5 (2)"]
#check @AdicCompletion.module_flat_of_quotient_flat_of_isZero_tor_one
