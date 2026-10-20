/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Generation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

-- Proposition 13.37.6: compact weak generation is the reusable compact-subcategory generation
-- criterion in the pretriangulated shared library.
@[stacks 09SR] #check @CategoryTheory.IsCompactObject.isCompactlyGenerated
#check @CategoryTheory.IsCompactObject.isClassicalTriangulatedGenerator
#check @CategoryTheory.IsCompactObject.isWeakGenerator
#check @CategoryTheory.IsCompactObject.isWeakGenerator_iff
