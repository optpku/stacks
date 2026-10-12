/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat.Stalk
import StacksCheckRecall

@[expose] public section

/- The reusable pointwise predicate is ordinary module flatness of the module-valued stalk. -/
#check @SheafOfModules.RingedSite.IsFlatAt

/- Lemma 18.39.2: a flat module sheaf has a flat stalk at every point. -/
@[stacks 05VB]
#check @SheafOfModules.RingedSite.IsFlat.atPoint
