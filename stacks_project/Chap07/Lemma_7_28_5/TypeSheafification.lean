module

public import ReasLib.CategoryTheory.Sites.LargeTypeSheafification
public import ReasLib.CategoryTheory.Sites.TypeSheafification.ULift
public import StacksCheckRecall.CommandCrossRef

/-!
# Type-valued sheafification recall

This former local proof layer is superseded by the reusable Type-valued
sheafification API in ReasLib.  It deliberately introduces no second owner
for the same statements.
-/

@[expose] public section

@[stacks 0D5R "Type-valued sheafification"] #check @CategoryTheory.GrothendieckTopology.toPlus_isLocallyInjective_type
#check @CategoryTheory.GrothendieckTopology.toPlus_isLocallySurjective_type
#check @CategoryTheory.GrothendieckTopology.toSheafify_isLocallyInjective_type_of_univLE
#check @CategoryTheory.GrothendieckTopology.toSheafify_isLocallySurjective_type
#check @CategoryTheory.GrothendieckTopology.type_WEqualsLocallyBijective_of_univLE
#check @CategoryTheory.GrothendieckTopology.uliftFunctor_preservesSheafification_of_WEqualsLocallyBijective
