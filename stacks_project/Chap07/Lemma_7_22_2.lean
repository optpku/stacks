module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint

/-!
# Lemma 7.22.2

The continuous-right-adjoint direct-image comparison is a reusable topos-level API, owned by
`Functor.ContinuousRightAdjoint` in ReasLib rather than by this Chapter 7 recall module.
-/

@[expose] public section

/- Lemma 7.22.2 (00XY): the continuous direct image of a continuous right adjoint agrees with
the cocontinuous direct image of its left adjoint. -/
@[stacks 00XY] #check @CategoryTheory.Functor.ContinuousRightAdjoint.pushforwardContinuousIso
