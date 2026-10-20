module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint

/-!
# Lemma 7.23.1

The lower-shriek comparisons for a continuous functor with a left adjoint are owned by the
neutral ReasLib topos layer.  This module retains the textbook entry as tagged recalls.
-/

@[expose] public section

/- Lemma 7.23.1 (08NH): the lower-shriek functor is compared with the sheaf functors induced by
a left adjoint, and the final direct-image comparison is the role-swapped continuous-right-adjoint
API. -/
@[stacks 08NH "(1)"] #check @CategoryTheory.Functor.LeftAdjoint.pullbackIsoCocontinuous
@[stacks 08NH "(2)"] #check @CategoryTheory.Functor.LeftAdjoint.pullbackExact
@[stacks 08NH "(3)"] #check @CategoryTheory.Functor.ContinuousLeftAdjoint.pullbackIsRightAdjoint
@[stacks 08NH "(4)"] #check @CategoryTheory.Functor.CocontinuousLeftAdjoint.pullbackIsoInverseImage
@[stacks 08NH "(5)"] #check @CategoryTheory.Functor.ContinuousRightAdjoint.pushforwardContinuousIso
