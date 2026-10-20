/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.Lift
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.42.4 support index

The old proof-route stages for Lemma 10.42.4 are intentionally not part of
the public aggregate.  The reusable owner is the neutral finite purely
inseparable lift API.

@stack 04KM
-/

@[stacks 04KM]
#check @FieldExtension.PurelyInseparable.Lift.existsOfEssFiniteType
