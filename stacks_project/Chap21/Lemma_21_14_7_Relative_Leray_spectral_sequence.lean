/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.RelativeLeray
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.14.7 (Relative Leray spectral sequence) (0734) is the source-facing recall of the
functorial relative Leray realization for composable morphisms of ringed topoi, formalized by
ringed sites.  The reusable realization, its classical `R^p g_* (R^q f_* F)` page, abutment,
maps, identity and composition laws, and bounded-below companion are owned by
`RingedSite.Hom.RelativeLeray`.
-/

namespace RingedSite.Hom

@[stacks 0734]
#check @RelativeLeray.functorial

@[stacks 0734]
#check @RelativeLeray.nonempty

@[stacks 0734]
#check @RelativeLeray.isAcyclic

@[stacks 0734]
#check @RelativeLeray.BoundedBelow.nonempty

@[stacks 0734]
#check @RelativeLeray.BoundedBelow.existsMap

end RingedSite.Hom

end
