/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Construction
import StacksCheckRecall

/-!
# Cech hypercovering associated to a cover

This source entry is the singleton-family specialization of the reusable Cech constructor.
-/

open CategoryTheory

/- Example 25.3.6 (Cech hypercovering associated to a cover): a covering arrow determines the
Cech hypercovering of its singleton family. -/
@[stacks 0GMA] #check @Hypercovering.cechOfArrow
