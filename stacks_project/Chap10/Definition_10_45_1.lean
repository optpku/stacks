/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.Generated.Properties
import StacksCheckRecall

@[expose] public section

/-!
# Perfect Fields

Definition 10.45.1 is a canonical recall of the mathlib class `PerfectField`.
Its Stacks-project characterization through `Algebra.IsSeparableOver` belongs
to the field-theory shared library.

@stack 030Y
-/

@[stacks 030Y]
#check @PerfectField

@[stacks 030Y]
#check @PerfectField.iff_forall_isSeparableOver
