/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Connected
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Lemma 21.39.5 (08Q7): for a category with an initial or final object, the derived lower-shriek
counit after constant inverse image is invertible on `D(AddCommGrpCat)` and on
`D(ModuleCat B)`. The coefficient-general connected-counit API is owned by
`CategoryTheory.DerivedColimit`. -/

@[stacks 08Q7 "abelian initial-or-final derived lower-shriek counit"]
#check @CategoryTheory.DerivedColimit.derivedColimitCounit_isIso_of_hasInitial_or_hasTerminal_abelian

@[stacks 08Q7 "module initial-or-final derived lower-shriek counit"]
#check @CategoryTheory.DerivedColimit.derivedColimitCounit_isIso_of_hasInitial_or_hasTerminal_module
