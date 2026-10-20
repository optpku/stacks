/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Complex.FiniteReplacement
import StacksCheckRecall

@[expose] public section

/-!
# Strict Filtered-Injective Resolutions

The reusable finite filtered-complex category, its inclusion and map lifts, and the replacement
theorem are owned by `ReasLib.CategoryTheory.Filtration.Complex.{FiniteCategory,FiniteReplacement}`.
-/

namespace CategoryTheory.FilteredComplex.StrictReplacement

/- Lemma 13.26.9: a bounded-below filtered complex with finite filtrations has a termwise strict
monomorphic filtered quasi-isomorphism to a bounded-below complex of filtered-injective objects. -/
@[stacks 05TW] #check
  @exists_of_finiteFiltrations

end CategoryTheory.FilteredComplex.StrictReplacement
