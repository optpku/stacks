/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/- General core: two dimension functions differ locally constantly on a locally Noetherian
quasi-sober space. -/
#check @IsDimensionFunction.isLocallyConstant_sub

/- General core: a locally constant translation characterizes dimension functions. -/
#check @IsDimensionFunction.isDimensionFunction_iff_sub_isLocallyConstant

/- Lemma 5.20.3: on a locally Noetherian sober topological space, two dimension functions differ
by a locally constant integer-valued function. -/
@[stacks 02IB]
#check @IsDimensionFunction.isLocallyConstant_sub_of_sober
