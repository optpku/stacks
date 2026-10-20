/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
