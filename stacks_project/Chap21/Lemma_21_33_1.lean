module

public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductCompatibility
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductComposition
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductNaive
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.33.1

Relative cup products and their compatibility laws are categorical constructions owned by
ReasLib.  This entry recalls the comparison with a naive tensor model and the adjacent reusable
laws without rebuilding their edge maps in the chapter.
-/

/- Lemma 21.33.1 (0FPK): the relative derived cup product agrees with the naive cup product after
passing between a concrete tensor model and the derived category. -/
@[stacks 0FPK]
#check @CategoryTheory.derivedPushforward_tensor_naiveCupProduct_commSq

#check @CategoryTheory.DerivedPushforwardTensorNaiveCup.commSqOfMate
#check @CategoryTheory.DerivedPushforwardTensorNaiveCup.top
#check @CategoryTheory.DerivedPushforwardTensorNaiveCup.left
#check @CategoryTheory.DerivedPushforwardTensorNaiveCup.right
#check @CategoryTheory.DerivedPushforwardTensorNaiveCup.bottom
#check @CategoryTheory.relativeDerivedCupProduct_commutative_commSq
#check @CategoryTheory.relativeDerivedCupProduct_comp_commSq
#check @CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated
#check @CategoryTheory.RelativeDerivedCupProductComp.source
#check @CategoryTheory.RelativeDerivedCupProductComp.target
#check @CategoryTheory.RelativeDerivedCupProductComp.iterated
