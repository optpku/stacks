/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Horseshoe
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.8

The finite filtered horseshoe is a reusable construction, so its structured witness is owned by
`CochainComplex.FilteredInjectivePlus.Horseshoe` in ReasLib rather than by this chapter facade.
-/

namespace CochainComplex.FilteredInjectivePlus

/- Lemma 13.26.8 (`05TV`): a short exact sequence of finite filtered objects, together with
degree-zero associated-graded quasi-isomorphisms to bounded-below filtered-injective complexes,
admits a termwise split filtered-injective horseshoe whose outer comparison maps are prescribed. -/
@[stacks 05TV] #check
  @exists_horseshoe

end CochainComplex.FilteredInjectivePlus
