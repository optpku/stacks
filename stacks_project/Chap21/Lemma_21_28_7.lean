/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CohomologyIn
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.28.7 (0D7W) is the local bounded-cohomology-basis refinement of Lemma 21.28.6.  The
pullback-specific basis is the explicit `RingedSite.Hom.PullbackBasis` datum; it is not replaced by
the site-only basis.  The reusable unit/counit criteria and the equivalence root are owned by
`RingedSite.Hom.moduleDerivedCohomologyIn`.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

namespace RingedSite.Hom.moduleDerivedCohomologyIn

@[stacks 0D7W]
#check @mapsPushforwardDerived_of_pullbackBasis

@[stacks 0D7W]
#check @pushforwardDerived_of_pullbackBasis

@[stacks 0D7W]
#check @unit_isIso_of_pullbackBasis

@[stacks 0D7W]
#check @counit_isIso_of_pullbackBasis

@[stacks 0D7W]
#check @unitCounit_isIso_of_pullbackBasis

@[stacks 0D7W]
#check @pullback_isEquivalence_of_pullbackBasis

end RingedSite.Hom.moduleDerivedCohomologyIn

@[stacks 0D7W]
#check @RingedSite.Hom.PullbackBasis

end
