/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.ZeroObject
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory.Limits

/- Definition 12.3.3: the notion of zero object is the canonical predicate `IsZero`. -/
@[stacks 0100] #check IsZero
#check IsZero.isInitial
#check IsZero.isTerminal

section

variable {C : Type u} [Category.{v} C]
variable {X : C}

#check IsInitial.isZero_of_isTerminal

end

end CategoryTheory.Limits
