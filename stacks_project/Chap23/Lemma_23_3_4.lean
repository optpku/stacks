/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.DividedPowers.Category.Colimits

@[expose] public section

open CategoryTheory.Limits

universe u

/- Lemma 23.3.4 (Tag 07GX): the category of divided power rings has all colimits. -/
@[stacks 07GX]
#check (DividedPowerRing.hasColimits : HasColimits DividedPowerRing.{u})
