/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Closure
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

/- Definition 5.21.1 (1): for a subset `T ⊆ X`, its interior is the canonical set `interior T`. -/
@[stacks 03HN "interior as the largest open subset"]
#check interior

/- Companion check: `interior T` is contained in `T`. -/
#check interior_subset

/- Companion check: every open subset of `T` is contained in `interior T`, so `interior T` is the
largest open subset of `X` contained in `T`. -/
#check interior_maximal

/- Definition 5.21.1 (2): the Stacks notion of a nowhere dense subset is the canonical predicate
`IsNowhereDense`, defined by `interior (closure T) = ∅`. -/
@[stacks 03HN "nowhere dense subsets via closure with empty interior"]
#check IsNowhereDense
