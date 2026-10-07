module

public import ReasLib.Algebra.Homology.DerivedCategory.Regular.HomologyGap
import StacksCheckRecall

/-!
# Lemma 15.80.4 (0FXK)

@stack 0FXK
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.80.4 (0FXK): a cohomology gap in a perfect complex splits its truncation triangle. -/
@[stacks 0FXK "Lemma 15.80.4"]
#check @exists_truncation_gap_biprod_of_isPerfect_of_homology_vanishing
