/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.DividedPowers.Category.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 23.3.2 (Tag 07GV), limits: the category of divided power rings has all limits. -/
@[stacks 07GV "all limits"]
#check (DividedPowerRing.hasLimits : HasLimits DividedPowerRing.{u})

/- Lemma 23.3.2 (Tag 07GV), underlying rings: the forgetful functor to commutative rings creates
limits. -/
@[stacks 07GV "underlying ring of a limit"]
#check (DividedPowerRing.forgetCommRing.createsLimits :
  CreatesLimits DividedPowerRing.forgetCommRing)
