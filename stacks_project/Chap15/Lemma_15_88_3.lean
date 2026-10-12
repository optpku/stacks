/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Grothendieck
import StacksCheckRecall

/-!
# Lemma 15.88.3

@stack 0CQD
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.88.3 (Stacks 0CQD): for a fixed ring `A`, the total right derived inverse-limit functor on
`DerivedCategory (SequentialInverseSystem (ModuleCat A))` has a derived-limit presentation for
its canonical stagewise tower. The presentation is noncanonical, so its correct formal content is
the shared `Nonempty (IsDerivedLimit ...)` theorem
`CategoryTheory.DerivedLimit.isDerivedLimit_of_tower`, rather than a chosen
public witness. -/
@[stacks 0CQD] #check @CategoryTheory.DerivedLimit.Stage.tower
#check @CategoryTheory.DerivedLimit.Stage.towerFunctor
#check @CategoryTheory.DerivedLimit.isDerivedLimit_of_tower
