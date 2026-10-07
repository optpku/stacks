module

public import ReasLib.CategoryTheory.Sites.Cech.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 21.8.1 (Tag 03AM): `cechComplex U family F` is the Cech complex of `F` for
the indexed family in `Over U`, and `cechCohomology U family F i` is its degree-`i`
cohomology object. -/
@[stacks 03AM "Cech complex"]
#check @CategoryTheory.cechComplex

@[stacks 03AM "Cech cohomology"]
#check @CategoryTheory.cechCohomology

/- The defining homology identification is available as a simp lemma. -/
#check @CategoryTheory.cechComplex_homology

end
