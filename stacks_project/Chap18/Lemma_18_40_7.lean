/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Rank.Invertible
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.7 (0B8Q), forward direction: finite locally free module sheaves of rank one are tensor
invertible. -/
@[stacks 0B8Q "forward"]
#check @SheafOfModules.RingedSite.rankOne_isInvertible

/- Lemma 18.40.7 (0B8Q), converse direction: under local unit dichotomy, tensor-invertible module sheaves have
rank one. -/
@[stacks 0B8Q "converse"]
#check @SheafOfModules.RingedSite.rankOne_of_isInvertible

#check @SheafOfModules.RingedSite.rankOne_iff_isInvertible
