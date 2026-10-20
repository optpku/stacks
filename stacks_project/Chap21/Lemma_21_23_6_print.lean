/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.StageComparison
import StacksCheckRecall

@[expose] public section

/- Historical print path for Lemma 21.23.6 (0D6L).  The named stage-projection criterion is
owned by ReasLib; keeping this path as a recall avoids a chapter-to-chapter dependency. -/
@[stacks 0D6L "stage projection injectivity criterion"]
#check @RingedSite.Hom.ModuleDerived.Limit.stageProjection_mono_of_cofinal

#check @CategoryTheory.IsDerivedLimit.stageProjection
#check @RingedSite.Hom.ModuleSections.Underlying.cohomologyTower
