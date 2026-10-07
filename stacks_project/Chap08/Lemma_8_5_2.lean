module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.5.2: a stack in groupoids is a stack on the site with groupoid fibers. -/
@[stacks 02ZJ]
#check @IsStack.InGroupoids.iff_stackOnSite_and_fibersGroupoid
#check @IsStack.InGroupoids.iff_fibered_and_stackOnSite

end CategoryTheory
