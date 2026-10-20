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
# Lemma 5.20.3

The reusable torsor-style API for dimension functions is owned by
`ReasLib.Topology.Specialization.Dimension.Catenary`.
-/

/- Lemma 5.20.3: on a locally Noetherian sober topological space, two dimension functions differ
by a locally constant integer-valued function. The sober `T₀` half is derived from the dimension
function (`IsDimensionFunction.t0Space`), so the quasi-sober owner is the source statement. -/
@[stacks 02IB]
#check @IsDimensionFunction.isLocallyConstant_sub

/- General core: a locally constant translation characterizes dimension functions. -/
#check @IsDimensionFunction.isDimensionFunction_iff_sub_isLocallyConstant
