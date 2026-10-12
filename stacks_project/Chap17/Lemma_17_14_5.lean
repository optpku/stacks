/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteLocallyFree.Morphism
import StacksCheckRecall

@[expose] public section

/- Lemma 17.14.5 (089Q): a morphism of finite locally free module sheaves of the same rank is an
isomorphism exactly when it is an epimorphism. -/
@[stacks 089Q]
#check @SheafOfModules.IsFiniteLocallyFreeOfRank.isIso_iff_epi

#check @SheafOfModules.IsFiniteLocallyFreeOfRank.isIso_of_epi
