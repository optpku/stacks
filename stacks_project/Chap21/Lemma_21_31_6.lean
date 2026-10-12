/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.LCCat.SmallToSlice
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.GrothendieckTopology

/- Lemma 21.31.6 (09X3), clause (1): the pullback-section rule is a qc sheaf. -/
@[stacks 09X3 "(1)"]
#check @LCCat.SmallToSlice.isSheafQc
@[stacks 09X3 "(1), objectwise sections"]
#check @LCCat.SmallToSlice.ruleObjIso
@[stacks 09X3 "(2), abstract pullback comparison"]
#check @LCCat.SmallToSlice.sectionsComparison
@[stacks 09X3 "(2), abstract pullback comparison isomorphism"]
#check @LCCat.SmallToSlice.sectionsComparison_isIso

/- Lemma 21.31.6 (09X3), clause (2): the rule is the Zariski inverse-image sheaf and its
identity-site direct image comparison is canonical. -/
@[stacks 09X3 "(2)"]
#check @LCCat.SmallToSlice.zar
@[stacks 09X3 "(2), direct-image comparison"]
#check @LCCat.SmallToSlice.pushforwardComparison
@[stacks 09X3 "(2), direct-image comparison isomorphism"]
#check @LCCat.SmallToSlice.pushforwardComparison_isIso

/- Lemma 21.31.6 (09X3), clause (3): the topology-comparison inverse image agrees with the qc
pullback-section sheaf through a canonical map. -/
@[stacks 09X3 "(3)"]
#check @LCCat.SmallToSlice.qc
@[stacks 09X3 "(3), comparison map"]
#check @LCCat.SmallToSlice.qcComparison
@[stacks 09X3 "(3), comparison isomorphism"]
#check @LCCat.SmallToSlice.qcComparison_isIso
