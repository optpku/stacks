/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Representable.Stack
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.13.1

The chapter entry is a recall of the neutral representable-slice stack criterion. The canonical
owner is set-valued; its groupoid-fibred and ordinary stack views are exported as forgetful
companions by ReasLib.
-/

namespace CategoryTheory

/- Lemma 8.13.1 (04WU): -/
@[stacks 04WU]
#check @Over.StackOnSite.iff_isSheaf

#check @Over.StackInSets.iff_isSheaf
#check @Over.PrestackOnSite.iff_isSeparated
#check @Over.representableStack
#check @Over.representableStack.total
#check @Over.representableStack.p
#check @Over.representableStack.toSets
#check @Over.representableStack.toGroupoids
#check @Over.representableStack.stack
#check @Over.representableStack.stack.total
#check @Over.representableStack.stack.p
#check @Over.representableStack.stack.projectionInSets

end CategoryTheory
