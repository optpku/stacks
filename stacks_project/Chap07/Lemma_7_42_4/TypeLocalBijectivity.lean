/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.LargeTypeSheafification
public import ReasLib.CategoryTheory.Sites.TypeSheafification.ULift
public import StacksCheckRecall.CommandCrossRef

/-!
# Type-local-bijectivity recall

The former Chapter 7 proof layer duplicated the canonical Type-valued
sheafification and universe-lift APIs.  Those APIs now live in ReasLib; this
legacy module intentionally introduces no competing declarations.
-/

@[expose] public section

@[stacks 04B8 "Type local bijectivity"] #check @CategoryTheory.GrothendieckTopology.toPlus_isLocallyInjective_type
#check @CategoryTheory.GrothendieckTopology.toPlus_isLocallySurjective_type
#check @CategoryTheory.GrothendieckTopology.toSheafify_isLocallyInjective_type_of_univLE
#check @CategoryTheory.GrothendieckTopology.toSheafify_isLocallySurjective_type
#check @CategoryTheory.GrothendieckTopology.type_WEqualsLocallyBijective_of_toSheafify_isLocallyInjective
#check @CategoryTheory.GrothendieckTopology.largeType_WEqualsLocallyBijective
#check @CategoryTheory.GrothendieckTopology.locallyInjective_of_whisker_ulift
#check @CategoryTheory.GrothendieckTopology.locallySurjective_of_whisker_ulift
