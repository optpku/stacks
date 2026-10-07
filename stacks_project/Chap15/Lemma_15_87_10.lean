module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
import StacksCheckRecall

/-!
# Lemma 15.87.10

@stack 07KY
-/

@[expose] public section

/- Lemma 15.87.10 (Stacks 07KY): the Milnor short exact sequence for the cohomology of a
derived limit is the shared consequence `CategoryTheory.IsDerivedLimit.cohomologyShortExact` of
its derived-limit witness. Its left term is the canonical `DerivedLimit.R1` of the preceding
cohomology tower. -/
@[stacks 07KY] #check @CategoryTheory.IsDerivedLimit.cohomologyShortExact
