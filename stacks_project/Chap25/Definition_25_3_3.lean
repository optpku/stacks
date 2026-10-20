/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
import StacksCheckRecall

/-!
# Hypercoverings

The reusable predicate and bundled object are owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget`.
-/

open CategoryTheory

/- Definition 25.3.3: a hypercovering has a covering degree-zero family and covering matching
maps in every degree. -/
@[stacks 01G5] #check @Hypercovering

#check @IsHypercovering
#check @Hypercovering.isHypercovering
