/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Catenary.Localization
import StacksCheckRecall

/-!
# Catenarity under localization

@stack 00NJ
-/

/- Lemma 10.105.4 (1): a localization of a catenary ring is catenary. -/
@[stacks 00NJ "(1)"]
#check @localization_isCatenaryRing

/- Lemma 10.105.4 (2): a localization of a universally catenary ring is universally
catenary. -/
@[stacks 00NJ "(2)"]
#check @localization_universallyCatenaryRing
