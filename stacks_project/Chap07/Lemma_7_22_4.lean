/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
