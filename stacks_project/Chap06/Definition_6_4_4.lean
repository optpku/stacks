/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Abelian
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat

universe u

open scoped TopCat

variable (X : TopCat.{u})

/- The canonical owner `TopCat.Presheaf` specialized to `AddCommGrpCat` simultaneously supplies
the sectionwise abelian groups, additive restriction maps, and natural transformations with
additive components. The notation `PAb(X)` is therefore only the source-facing name for this exact
specialization, avoiding a parallel wrapper while remaining reusable throughout the chapter. -/

/- Definition 6.4.4: an abelian presheaf on `X` is an `AddCommGrpCat`-valued presheaf, its
morphisms are natural transformations in that category, and their category is denoted `PAb(X)`. -/
@[stacks 006K "abelian presheaves and their morphisms as AddCommGrpCat-valued presheaves"]
recall TopCat.Presheaf
