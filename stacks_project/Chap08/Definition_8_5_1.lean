module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.5.1 — Bridge

Definition 8.5.1 is the stack-in-groupoids condition. The canonical owner is now
`CategoryTheory.IsStack.InGroupoids` in `CategoryTheory/Fibered/Stack/InGroupoids.lean`.
-/

namespace CategoryTheory

@[stacks 02ZI]
#check @IsStack.InGroupoids

#check @IsStack.InGroupoids.toInGroupoids
#check @IsStack.InGroupoids.toIsStack
#check @IsStack.InGroupoids.toOnSite
#check @IsStack.InGroupoids.iff_fibered_and_stackOnSite
#check @IsStack.InGroupoids.iff_stackOnSite_and_fibersGroupoid

end CategoryTheory
