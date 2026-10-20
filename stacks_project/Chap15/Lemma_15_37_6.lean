/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Basic
import StacksCheckRecall

/-!
# Lemma 15.37.6 (07EE)

@stack 07EE
-/

@[expose] public section

/- Lemma 15.37.6 (07EE): adic formal smoothness persists when the target ideal is enlarged. -/
@[stacks 07EE "monotonicity of adic formal smoothness"]
#check @RingHom.formally_smooth_for_adic_of_le
