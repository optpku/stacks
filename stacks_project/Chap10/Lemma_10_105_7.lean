/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Catenary.Quotient
import StacksCheckRecall

/-!
# Catenarity under quotients

@stack 00NK
-/

/- Lemma 10.105.7 (1): a quotient of a catenary ring is catenary. -/
@[stacks 00NK "(1)"]
#check @quotient_catenaryRing

/- Lemma 10.105.7 (2): a quotient of a universally catenary ring is universally
catenary. -/
@[stacks 00NK "(2)"]
#check @quotient_universallyCatenaryRing
