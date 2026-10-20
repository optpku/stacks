/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.FiniteFreeRetract
import StacksCheckRecall

@[expose] public section

/- Lemma 17.14.6 (0BCI): a direct summand of a finite locally free module sheaf on a locally
ringed space is finite locally free. -/
@[stacks 0BCI]
#check @SheafOfModules.IsFiniteLocallyFree.ofRetract

/- The reusable owner identifies finite local freeness with the generic local
finite-free-retract property. -/
#check @SheafOfModules.RingedSite.FiniteFreeRetract.isLocal_iff_isFiniteLocallyFree
