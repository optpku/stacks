/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
import StacksCheckRecall

@[expose] public section

/- Lemma 17.28.2 (08RM): relative derivations into module sheaves are represented by the
site-generic sheaf of relative differentials. -/
@[stacks 08RM]
#check @SheafOfModules.RingedSite.relativeDifferentials_representsDerivations

#check @SheafOfModules.RingedSite.relativeDifferentialDesc
#check @SheafOfModules.RingedSite.relativeDifferentialDesc_fac
#check @SheafOfModules.RelativeDerivation.functor
#check @SheafOfModules.RingedSite.RelativeDifferentials.homEquiv
#check @SheafOfModules.RingedSite.RelativeDifferentials.corepresentableBy
#check @SheafOfModules.RingedSite.RelativeDifferentials.representingIso
