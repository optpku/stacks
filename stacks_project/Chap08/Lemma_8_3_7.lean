/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Refinement
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.3.7: effective descent passes from a fine family to a coarser family when the
restrictions to coarse members are fully faithful and the restrictions to pairwise overlaps are
faithful. -/
@[stacks 0GEA]
#check @DescentDatum.Refinement.canonicalFunctor_isEquivalence

/- The full and faithful parts of the local-refinement argument are available independently. -/
#check @DescentDatum.Refinement.pullFunctor_faithful
#check @DescentDatum.Refinement.pullFunctor_full

/- Same-target refinements and componentwise base change use their canonical ReasLib owners. -/
#check @DescentDatum.Pullback.functorOfRefinement
#check @SemiRepresentableFamily.Over.baseChange
#check @SemiRepresentableFamily.Over.baseChangeTo

end CategoryTheory
