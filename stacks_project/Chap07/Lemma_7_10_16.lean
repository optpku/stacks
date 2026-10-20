module

public import ReasLib.CategoryTheory.Sites.TypeSheafification
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.10.16 recall

The reusable `Type`-valued sheafification representation API belongs to
ReasLib. This source file retains only the labeled textbook recall.
-/

@[expose] public section

/- Lemma 7.10.16 (00WK): every section of `J.sheafify F` has a two-stage
local representation by matching families of sections of `F`, and matching
families glue uniquely to sheafified sections. -/
@[stacks 00WK] #check @CategoryTheory.GrothendieckTopology.Sheafify.existsNestedPlusRepresentation

/- The inner representatives agree after a covering refinement on each outer overlap; this is
the source's intermediate family of covers `U_ijk`. -/
@[stacks 00WK "overlap refinement covers"]
#check @CategoryTheory.GrothendieckTopology.Sheafify.overlapRefinement

/- The refined matching family glues to a unique sheafified section. -/
@[stacks 00WK "unique glued section"]
#check @CategoryTheory.GrothendieckTopology.Sheafify.existsUniqueSectionOfMatching
