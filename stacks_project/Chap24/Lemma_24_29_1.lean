/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.KInjective.RightDerived
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.29.1

K-injective resolutions provide the reusable right-derived owner, its canonical functor and unit,
and the pointwise computation theorem.  The complete checks keep all site and target-category
assumptions visible without rebuilding local instances in this chapter file.
-/

open SheafOfModules.RingedSite.DifferentialGradedModule

@[stacks 0FTN] #check @Functor.RightDerived.exists_of_exact
#check @Functor.RightDerived.hasRightDerivedFunctor
#check @Functor.RightDerived.functor
#check @Functor.RightDerived.unit
#check @Functor.RightDerived.isRightDerived
#check @Functor.RightDerived.computesAt_of_gradedInjective
