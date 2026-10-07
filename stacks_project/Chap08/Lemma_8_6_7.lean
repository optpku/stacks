module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Thin
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.6.7: if one leg into a stack in groupoids is faithful and the other source is a
stack in setoids, their canonical two-fibre product is a stack in setoids.  The general owner
only assumes setoid fibers on the second source. -/
@[stacks 05UI] #check @StackOver.Groupoids.TwoFibreProduct.isStackInSetoids_of_left
#check @StackOver.Groupoids.TwoFibreProduct.isStackInSetoids_of_left_of_faithful

/- The symmetric right-leg form avoids forcing consumers to swap the cospan manually. -/
#check @StackOver.Groupoids.TwoFibreProduct.isStackInSetoids_of_right
#check @StackOver.Groupoids.TwoFibreProduct.isStackInSetoids_of_right_of_faithful

/- The reusable proof is split into the fiberwise thinness statement and the resulting
fibered-in-setoids statement. -/
#check @StackOver.Groupoids.TwoFibreProduct.fiber_isThin_of_left
#check @StackOver.Groupoids.TwoFibreProduct.fiber_isThin_of_left_of_faithful
#check @StackOver.Groupoids.TwoFibreProduct.isFiberedInSetoids_of_left
#check @StackOver.Groupoids.TwoFibreProduct.isFiberedInSetoids_of_left_of_faithful
#check @StackOver.Groupoids.TwoFibreProduct.fiber_isThin_of_right
#check @StackOver.Groupoids.TwoFibreProduct.fiber_isThin_of_right_of_faithful
#check @StackOver.Groupoids.TwoFibreProduct.isFiberedInSetoids_of_right
#check @StackOver.Groupoids.TwoFibreProduct.isFiberedInSetoids_of_right_of_faithful

end CategoryTheory
