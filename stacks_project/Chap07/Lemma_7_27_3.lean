module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Localization.Basic
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint

/-!
# Lemma 7.27.3

Relocalization direct image is the `Over.map f ⊣ Over.pullback f` specialization of the generic
continuous-right-adjoint direct-image comparison.
-/

@[expose] public section

/- Lemma 7.27.3 (00Y3): the relocalization direct image and its section formula are supplied by
the canonical `Over.map f ⊣ Over.pullback f` adjunction and the generic
continuous-right-adjoint comparison. -/
@[stacks 09W9] #check @CategoryTheory.Functor.ContinuousRightAdjoint.pushforwardContinuousIso

/- The relocalization adjunction supplies the pullback object used in the section formula. -/
#check @CategoryTheory.Over.mapPullbackAdj
