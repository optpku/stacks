/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Henselization.BaseChange.AtPrime
import StacksCheckRecall

@[expose] public section

/-!
# At-prime base change of henselizations

Lemma 10.155.8 is recalled from the explicit-comparison API.  The tensor
local target and its prime are neutral localization constructions; the sole
henselization-specific statement is the final owner theorem.

@stack 08HU
-/

/- Lemma 10.155.8, tag `08HU`: for an explicit local comparison between
henselizations of `Localization.AtPrime p` and `Localization.AtPrime q`, the
target is the henselization of the localization of `Rh ⊗[R] S` at the prime
selected by that local target. -/
@[stacks 08HU]
#check @Localization.AtPrime.LocalTarget.tensorMap
#check @Localization.AtPrime.LocalTarget.tensorPrime
#check @Localization.AtPrime.LocalTarget.localizedMap
#check @Localization.AtPrime.LocalTarget.localizedAlgebra
#check @IsHenselizationOf.BaseChange.AtPrime.Tensor.isHenselizationOf
