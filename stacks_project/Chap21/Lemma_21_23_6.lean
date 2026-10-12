/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.StageComparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.23.6

The local injectivity criterion is owned by the canonical stage-projection API in ReasLib; the
chapter no longer rebuilds a parallel comparison map.
-/

open RingedSite.Hom.ModuleDerived.Limit

/- Lemma 21.23.6 (0D6L): the canonical stage projection is mono on sections of the indicated
cohomology sheaf under the cofinal-cover hypotheses. -/
@[stacks 0D6L]
#check @stageProjection_mono_of_cofinal

#check @CategoryTheory.IsDerivedLimit.stageProjection
#check @RingedSite.Hom.ModuleSections.Underlying.cohomologyTower
