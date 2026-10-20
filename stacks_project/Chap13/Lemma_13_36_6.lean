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

-- Lemma 13.36.6: finite-stage comparison and the upgrade from a classical to a strong
-- triangulated generator are reusable generation API.
@[stacks 0FXA] #check @CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator.exists_stage_mem
#check @CategoryTheory.ObjectProperty.Generated.Stage.one_le_of_mem
#check @CategoryTheory.ObjectProperty.Generated.Stage.le_mul
#check @CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator.isStrong
