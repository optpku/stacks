/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat.Continuous
import StacksCheckRecall

@[expose] public section

/-!
# K-flatness under pullback

The reusable statement is owned by the continuous-presentation pullback API.  Its output-site
enough-points assumption is precisely what turns the stalkwise base-change calculation into a
global K-flatness assertion.
-/

/- Lemma 21.18.7: pullback along a continuous presentation of a morphism of ringed topoi
preserves K-flat cochain complexes when the output site has enough points. -/
@[stacks 0DEP]
#check @SheafOfModules.RingedSite.modulePullbackComplex.isKFlat_of_hasEnoughPoints

#check @SheafOfModules.RingedSite.moduleStructureMap
#check @SheafOfModules.RingedSite.modulePullback
#check @SheafOfModules.RingedSite.modulePullbackComplex
