/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Specialization.Dimension.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.20.2

Dimension-function catenarity and codimension APIs are owned by
`ReasLib.Topology.Specialization.Dimension.Catenary`. The source's sober hypothesis is
`[QuasiSober X] [T0Space X]`; the `T₀` half is derived from the dimension function by
`IsDimensionFunction.t0Space`, so the quasi-sober owners cover the source statement directly.
-/

/- Lemma 5.20.2 (1): a sober space with a dimension function is catenary. -/
@[stacks 02IA "catenarity from a dimension function"]
#check @IsDimensionFunction.catenarySpace

/- Lemma 5.20.2 (2): for `x ⤳ y`, `δ x - δ y` is the codimension of the point closures. -/
@[stacks 02IA "codimension formula for specialized point closures"]
#check @IsDimensionFunction.sub_eq_codimBetween_pointClosure
