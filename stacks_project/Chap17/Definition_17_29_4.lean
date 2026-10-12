/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
