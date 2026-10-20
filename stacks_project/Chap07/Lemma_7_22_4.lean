module

public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint

import StacksCheckRecall

@[expose] public section

/-!
[stacks 09VR]

Lemma 7.22.4 records the cocontinuity and site-morphism consequences of a continuous right
adjoint.
-/

@[stacks 09VR "cocontinuity"] #check CategoryTheory.Functor.ContinuousRightAdjoint.left_isCocontinuous
@[stacks 09VR "morphism of sites"] #check CategoryTheory.Functor.ContinuousRightAdjoint.right_isMorphismOfSites
