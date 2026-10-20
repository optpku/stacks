/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Basic
import StacksCheckRecall

/-!
Definition 15.37.3 (07NI): adic formal smoothness is represented by the reusable
`RingHom.formally_smooth_for_adic` predicate. This chapter file is a source facade.
@stack 07NI
-/

@[expose] public section

/- Definition 15.37.3, tag `07NI`: formal smoothness for an adic topology. -/
@[stacks 07NI "adic formal smoothness"]
#check @RingHom.formally_smooth_for_adic
