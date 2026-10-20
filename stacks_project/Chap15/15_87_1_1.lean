module

public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat.Sequential
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Tower
import StacksCheckRecall

/-!
# 15.87.1.1

@stack 08U4
-/

@[expose] public section

open CategoryTheory

/- 15.87.1.1 (Stacks 08U4): the right-derived inverse-limit functor on
`D(Ab(ℕ))` is the canonical specialization of `DerivedLimit.functor`.  The stagewise evaluation
and derived tower are recalled from the neutral sequential-limit API; no chapter-owned notation is
introduced. -/
@[stacks 08U4]
#check
  (DerivedLimit.functor AddCommGrpCat :
    DerivedCategory (SequentialInverseSystem AddCommGrpCat) ⥤ DerivedCategory AddCommGrpCat)

#check @DerivedLimit.Stage.evaluation
#check @DerivedLimit.Stage.derivedEvaluation
#check @DerivedLimit.Stage.tower
#check @DerivedLimit.Stage.towerFunctor
#synth HasDerivedCategory (SequentialInverseSystem AddCommGrpCat)
