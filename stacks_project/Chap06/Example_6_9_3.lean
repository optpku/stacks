/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.ContinuousFunctions.Real
import StacksCheckRecall

@[expose] public section

/- Example 6.9.3: the presheaf `U ↦ C(U, ℝ)` of continuous real-valued functions on `X`,
viewed as a presheaf of `ℝ`-algebras, satisfies the sheaf condition. -/
@[stacks 0074]
#check TopCat.ContinuousFunctions.presheaf_isSheaf ℝ
