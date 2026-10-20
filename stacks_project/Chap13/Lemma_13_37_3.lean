/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.37.3

The textbook resolution is represented by the neutral
`GeneratingFamilyResolution` data owner.  Its existence is the compact
generation theorem in the corresponding ReasLib leaf.
-/

#check @CategoryTheory.GeneratingFamilyResolution
#check @CategoryTheory.GeneratingFamilyResolution.sequence

@[stacks 09SN] #check @CategoryTheory.GeneratingFamilyResolution.nonempty
