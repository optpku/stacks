/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
import StacksCheckRecall

namespace CategoryTheory

/- Remark 25.3.8: `Hypercovering J X` is explicitly equivalent to the subtype of all simplicial
fixed-target families satisfying `IsHypercovering J`, not merely a chosen cofinal subsystem. -/
@[stacks 01G8] #check
  @Hypercovering.equivSubtype

end CategoryTheory
