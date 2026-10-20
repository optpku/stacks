/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CohomologyIn.BoundedBelow
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.28.5 (0D7U) is the source-facing recall of the bounded-below
cohomology-in pullback--pushforward interface. The reusable property, full
subcategory, restricted functors, adjunction, and equivalence criterion are
owned by `RingedSite.Hom.moduleDerivedCohomologyIn.Plus`.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

namespace RingedSite.Hom.moduleDerivedCohomologyIn.Plus

@[stacks 0D7U]
#check @RingedSite.Hom.modulePlusCohomologyIn

@[stacks 0D7U]
#check @RingedSite.Hom.ModulePlusCohomologyIn

@[stacks 0D7U]
#check @pullback

@[stacks 0D7U]
#check @mapsPullbackDerived

@[stacks 0D7U]
#check @pullbackDerived

@[stacks 0D7U]
#check @mapsPushforwardDerived

@[stacks 0D7U]
#check @pushforwardDerived

@[stacks 0D7U]
#check @adjunction

@[stacks 0D7U]
#check @unit_isIso

@[stacks 0D7U]
#check @counit_isIso

@[stacks 0D7U]
#check @pullback_isEquivalence

end RingedSite.Hom.moduleDerivedCohomologyIn.Plus

end
