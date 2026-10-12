/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Catenary
import StacksCheckRecall

/-!
# Lemma 10.105.9

The Cohen--Macaulay criteria for universal catenarity live in
`ReasLib.RingTheory.CohenMacaulay.Catenary`.

@stack 00NM
-/

/- Lemma 10.105.9 (1): a Noetherian Cohen--Macaulay ring is universally catenary. -/
@[stacks 00NM "(1)"]
#check @universallyCatenaryRing_of_cohenMacaulayRing

/- Lemma 10.105.9 (2): more generally, a full-support locally Cohen--Macaulay module
over a Noetherian ring makes the ring universally catenary. -/
@[stacks 00NM "(2)"]
#check @universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay
