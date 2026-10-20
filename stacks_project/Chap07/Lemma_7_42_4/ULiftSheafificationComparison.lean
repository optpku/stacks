module

public import ReasLib.CategoryTheory.Sites.TypeSheafification.ULift
public import StacksCheckRecall.CommandCrossRef

/-!
# ULift sheafification comparison recall

The universe-lift preservation criteria are reusable site APIs, not
Lemma 7.42.4-specific declarations.  Their canonical owner is ReasLib.
-/

@[expose] public section

@[stacks 04B8 "ULift sheafification comparison"] #check @CategoryTheory.GrothendieckTopology.uliftFunctor_hasSheafCompose_type
#check @CategoryTheory.GrothendieckTopology.uliftFunctor_preservesSheafification_of_toSheafify_isLocallyInjective
#check @CategoryTheory.GrothendieckTopology.uliftFunctor_preservesSheafification_of_WEqualsLocallyBijective
#check @CategoryTheory.GrothendieckTopology.uliftFunctor_preservesSheafification_of_multicospanLimits_and_coverColimits
#check @CategoryTheory.GrothendieckTopology.uliftFunctor_preservesSheafification_of_smallMulticospans_and_covers
