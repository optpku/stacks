/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.Profinite.Basic
import StacksCheckRecall

@[expose] public section

/- The source assertion is represented at the categorical owner layer. `Profinite.limitCone` and
`Profinite.limitConeIsLimit` give diagram-specific data, while `Profinite.toTopCat.createsLimits`
explains compatibility with limits of topological spaces; `Profinite.hasLimits` packages exactly
the reusable conclusion that every profinite-valued diagram has a limit in `Profinite`. -/

/- Lemma 5.22.3: a limit of profinite spaces is profinite. -/
@[stacks 0ET8 "limits of profinite spaces are profinite"]
#check Profinite.hasLimits
