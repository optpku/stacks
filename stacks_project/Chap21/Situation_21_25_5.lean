/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Hom.BoundedCohomologyBasis
import StacksCheckRecall

@[expose] public section

/-!
Situation `21.25.5` is a source-facing recall.  Its pullback-specific data owner is
`RingedSite.Hom.BoundedCohomologyBasis` in ReasLib; it is distinct from the site-generic basis in
`CategoryTheory.GrothendieckTopology` because the vanishing is evaluated after `f.base`.
-/

open CategoryTheory CategoryTheory.Limits

namespace RingedSite.Hom

@[stacks 0D6V] #check @BoundedCohomologyBasis
@[stacks 0D6V] #check @PullbackBasis

end RingedSite.Hom

end
