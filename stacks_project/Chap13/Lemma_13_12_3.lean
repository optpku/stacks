/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.ShortExact.DegreewiseSplit
import StacksCheckRecall

@[expose] public section

/- Lemma 13.12.3 (`0154`): the neutral API separates the canonical `Qh`-to-`Q` comparison Iso,
distinguishedness of the image triangle, and the final uniqueness-up-to-isomorphism statement. -/
@[stacks 0154] #check
  @CategoryTheory.DerivedCategory.ShortExact.degreewiseSplitImageIso
@[stacks 0154] #check
  @CategoryTheory.DerivedCategory.ShortExact.degreewiseSplitImage_distinguished
@[stacks 0154] #check
  @CategoryTheory.DerivedCategory.ShortExact.triangle_isomorphic_degreewiseSplitImage
