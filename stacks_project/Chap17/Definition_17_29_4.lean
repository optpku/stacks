/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction
import StacksCheckRecall

@[expose] public section

/- Definition 17.29.4 (0G3T): the canonical sheaf corepresenting differential operators of
order at most `k` is the `k`-th principal-parts module. -/
@[stacks 0G3T]
#check @SheafOfModules.RingedSite.PrincipalParts.sheaf

#check @SheafOfModules.RingedSite.PrincipalParts.corepresentation
