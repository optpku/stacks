/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.Ring
import StacksCheckRecall

@[expose] public section

/-!
# Normal Ring Predicate Recall

The source definition is the canonical `IsNormalRing` predicate in ReasLib.

@stack 00GV
-/

/- Definition 10.37.11 (Stacks tag `00GV`): a commutative ring is normal if for every prime
ideal `p`, the localization `Localization.AtPrime p` is a normal domain.

Owner: `IsNormalRing` in `ReasLib.RingTheory.Normal.Ring`. -/
@[stacks 00GV]
#check @IsNormalRing
#check @IsNormalRing.isDomain_localizationAtPrime
#check @IsNormalRing.isIntegrallyClosed_localizationAtPrime
