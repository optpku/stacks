/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Abelian
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import ReasLib.Topology.Sheaf.BaseChange.Proper
public import ReasLib.Topology.Sheaf.Derived.BaseChange.Proper
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.31.7 (0DCU) is the canonical small-to-slice comparison for an object of `LCCat`.  The
chapter facade fixes the source's `X`, `π_X = LCCat.opensOver X`, and abelian coefficient universe;
it does not expose arbitrary site functors or rebuild derived-category instances locally.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open TopologicalSpace
open scoped CategoryTheory.GrothendieckTopology

/- Lemma 21.31.7 (1): the objectwise cohomology comparison. -/
@[stacks 0DCU "(1)"]
#check @LCCat.SmallToSlice.cohomology_isomorphic

/- Lemma 21.31.7 (2): the small-to-slice direct image is exact. -/
@[stacks 0DCU "(2)"]
#check @LCCat.SmallToSlice.abPushforward_exact

/- Lemma 21.31.7 (3): the unit of the small-to-slice adjunction is invertible. -/
@[stacks 0DCU "(3)"]
#check @LCCat.SmallToSlice.abUnit_isIso

/- Lemma 21.31.7 (4): the canonical unit on the unbounded derived category is invertible. -/
@[stacks 0DCU "(4)"]
#check @LCCat.SmallToSlice.derivedUnit_isIso

/- The site-level square used in clause (5) is the reusable comparison owner. -/
@[stacks 0DCU "(5)"]
#check @LCCat.SmallToSlice.opensOver_compIso

/- Lemma 21.31.7 (6): the bounded-below comparison retains `f`, `L`, and the cohomological
degree in its reusable owner. -/
@[stacks 0DCU "(6)"]
#check @LCCat.SmallToSlice.hypercohomology_isomorphic

/- Lemma 21.31.7 (7): proper base change is supplied by the generic sheaf owner. -/
@[stacks 0DCU "(7a)"]
#check @TopCat.Sheaf.BaseChange.map_isIso_of_proper

@[stacks 0DCU "(7b)"]
#check @TopCat.Sheaf.BoundedBaseChange.IsMap.isIso_of_proper

end
