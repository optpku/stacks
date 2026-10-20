/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedCohomology
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.25.4 (0D6U).  The reusable owners live in
`RingedSite.Hom.modulePushforwardDerived`.  The two source clauses are exposed as separate,
fine-grained statements: the first is the landing property for `Rf_*`, and the second is the
degreewise lower-truncation comparison.  The relative predicates expand to the objectwise
higher-direct-image conditions through `Functor.mapsRightDerived_iff` and
`Functor.hasCohomologicalDimensionLEOn_iff`.
-/

open CategoryTheory

/- Lemma 21.25.4 (1): the bounded-basis landing property for `Rf_*`. -/
@[stacks 0D6U]
#check @RingedSite.Hom.modulePushforwardDerived.obj_mem_of_boundedBasis

/- Lemma 21.25.4 (2): the lower-truncation comparison isomorphism in the range
`N - (n : ℤ) ≤ j`. -/
@[stacks 0D6U]
#check @RingedSite.Hom.modulePushforwardDerived.homologyMap_isIso_of_boundedBasis

#check @RingedSite.Hom.modulePushforwardDerived.lowerStageMap
#check @CategoryTheory.Functor.mapsRightDerived_iff
#check @CategoryTheory.Functor.hasCohomologicalDimensionLEOn_iff

end
