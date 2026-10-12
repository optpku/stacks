/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
import StacksCheckRecall

@[expose] public section

/- The source has two independent global typeclass clauses. The size-indexed instances
`TopCat.topCat_hasLimitsOfSize` and `TopCat.forget_preservesLimitsOfSize` are the underlying
universe-polymorphic implementations, while `TopCat.topCat_hasLimits` and
`TopCat.forget_preservesLimits` are the exact all-shapes interfaces stated by the source.
Recalling the latter separately recovers both source clauses without local wrappers and makes the
instances directly available to downstream typeclass search. -/

/- Lemma 5.14.1 (1): the category of topological spaces has all limits. -/
@[stacks 08ZT "topological spaces have all limits"]
#check TopCat.topCat_hasLimits

/- Lemma 5.14.1 (2): the forgetful functor from topological spaces to types preserves all
limits. -/
@[stacks 08ZT "the forgetful functor from topological spaces preserves all limits"]
#check TopCat.forget_preservesLimits
