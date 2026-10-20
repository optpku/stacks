/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Generation.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

-- Lemma 13.36.5: weak generation is the reusable consequence of the canonical classical
-- triangulated-generator predicate.
@[stacks 09SL] #check @CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator.isWeak
