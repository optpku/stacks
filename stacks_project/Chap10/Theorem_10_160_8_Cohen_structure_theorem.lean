/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.CohenPresentation
import StacksCheckRecall

/-!
# Cohen structure theorem

The two source conclusions are owned separately: coefficient-subring existence belongs to
`Completion.CoefficientRing`, while the finite-variable power-series presentation belongs to
`Completion.CohenPresentation`.

@stack 032A
-/

@[expose] public section

@[stacks 032A "(1), existence of a coefficient ring"]
#check @IsCompleteLocalRing.exists_coefficientSubring

@[stacks 032A "(2), power-series quotient presentation"]
#check @IsCompleteLocalRing.exists_mvPowerSeries_quotient
