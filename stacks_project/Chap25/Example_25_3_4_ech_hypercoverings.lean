/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Construction
import StacksCheckRecall

/-!
# Cech hypercoverings

The reusable construction is owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Construction`.
-/

open CategoryTheory

/- Example 25.3.4 (Cech hypercoverings): a covering fixed-target family determines its Cech
hypercovering. -/
@[stacks 01G6] #check @Hypercovering.cech
