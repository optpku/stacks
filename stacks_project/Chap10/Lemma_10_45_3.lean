/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.Lift.Realization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.45.3

The source statement is a direct recall of the shared finite purely
inseparable realization API.  Its three conclusions are deliberately exposed
from one witness rather than as unrelated existential statements.

@stack 030R
-/

@[stacks 030R "finite purely inseparable realization"]
#check @FieldExtension.PurelyInseparable.Lift.Realization.existsOfEssFiniteType

@[stacks 030R "separable-over consequence"]
#check @FieldExtension.PurelyInseparable.Lift.isSeparableOver

@[stacks 030R "compositum consequence"]
#check @FieldExtension.PurelyInseparable.Lift.Realization.fieldRange_sup_eq_top

@[stacks 030R "reduced tensor-product realization"]
#check @FieldExtension.PurelyInseparable.Lift.Realization.reducedTensorAlgEquiv
