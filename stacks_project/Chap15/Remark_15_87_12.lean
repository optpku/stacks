module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.KInjective
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Uniqueness
import StacksCheckRecall

/-!
# Remark 15.87.12

@stack 08U5
-/

@[expose] public section

open CategoryTheory

/-
Remark 15.87.12 [08U5]. A sequential tower in `DerivedCategory AddCommGrpCat` can be lifted to a
tower of cochain complexes using the stage-tower essential-surjectivity owner. Any two resulting
derived limits are isomorphic over all stage projections, so the construction is independent of
the lift. The degree-`p` Milnor short exact sequence is then the canonical
`IsDerivedLimit.cohomologyShortExact` statement.
-/

/- Remark 15.87.12 (1): sequential derived towers admit compatible cochain-complex lifts. -/
@[stacks 08U5 "sequential derived towers admit cochain lifts"]
#check @CategoryTheory.DerivedLimit.Stage.TowerFunctor.essSurj_of_enoughInjectives

/- Remark 15.87.12 (2): two derived limits are isomorphic over every stage projection. -/
@[stacks 08U5 "derived limits are independent of the chosen lift"]
#check @CategoryTheory.IsDerivedLimit.existsIsoOverStages

/- Remark 15.87.12 (3): cohomology of a derived limit fits into the Milnor short exact sequence. -/
@[stacks 08U5]
#check @CategoryTheory.IsDerivedLimit.cohomologyShortExact

end
