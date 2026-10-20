/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/- Lemma 23.3.2 (Tag 07GV), underlying rings: the forgetful functor to commutative rings preserves
limits. -/
@[stacks 07GV "underlying ring of a limit"]
#check (DividedPowerRing.forgetCommRing.preservesLimits :
  PreservesLimits DividedPowerRing.forgetCommRing)
