module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Enough

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

/- Lemma 7.38.3 (00YM): an indexed family of points is conservative exactly when germs at its
points separate unequal local sections.  This is the indexed specialization of the reusable
separating-sections criterion. -/
@[stacks 00YM] #check @PointFamily.isConservative_iff_separatingSections

end CategoryTheory.GrothendieckTopology
