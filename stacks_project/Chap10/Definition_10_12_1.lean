/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.BilinearMap.Characterization
import StacksCheckRecall

@[expose] public section

/-! @stack 00CW -/

/- Definition 10.12.1 (Tag 00CW): bilinearity is owned by Mathlib's
`IsBilinearMap`, with the source's partial-linearity formulation exposed by
the reusable characterization API. -/
@[stacks 00CW]
#check @IsBilinearMap

@[stacks 00CW]
#check @IsBilinearMap.iff_isLinearMap
@[stacks 00CW]
#check @IsBilinearMap.iff_isLinearMap_curry
#check @IsBilinearMap.toLinearMap
