/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 17.18.3 (08BL): a flat finitely presented module sheaf is a retract of a finite free
module sheaf on a neighborhood of every point. -/
@[stacks 08BL]
#check @AlgebraicGeometry.RingedSpace.Modules.existsNeighborhoodRetract

-- The geometric theorem specializes the reusable ringed-site local-property criterion.
#check @SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal.ofIsFinitePresentationOfFlat

-- The reusable owner also exposes both converse implications and the symmetric criterion.
#check @SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal.isFinitePresentation
#check @SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal.isFlat
#check @SheafOfModules.RingedSite.FiniteFreeRetract.isLocal_iff_finitePresentation_and_flat
