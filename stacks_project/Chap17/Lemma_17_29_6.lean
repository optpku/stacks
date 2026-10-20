/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder
import StacksCheckRecall

@[expose] public section

/- Lemma 17.29.6 (0G3V): the canonical first-principal-parts sequence is short exact and
functorial in the module sheaf. -/
@[stacks 0G3V]
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.shortExact

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.sequenceFunctor

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.cotangentComparisonNatIso
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.CotangentComparison.natTrans
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.CotangentComparison.invNatTrans
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.CotangentComparison.hom_inv_id
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.CotangentComparison.inv_hom_id

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.sequenceIso

#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.sequenceNatIso
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.SequenceComparison.natTrans
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.SequenceComparison.invNatTrans
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.SequenceComparison.hom_inv_id
#check @SheafOfModules.RingedSite.PrincipalParts.FirstOrder.SequenceComparison.inv_hom_id
