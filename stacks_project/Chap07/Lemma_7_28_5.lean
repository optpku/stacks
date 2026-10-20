module

public import ReasLib.CategoryTheory.Sites.CostructuredArrowTopology.Topos
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.28.5

The comma-site topology and its direct-image comparison are owned by ReasLib;
this Chapter 7 file is the source-facing recall block.
-/

@[expose] public section

namespace CategoryTheory

/- Lemma 7.28.5 (0D5R): for a cocontinuous functor `u : C ⥤ D` and `V : D`,
the comma site `CostructuredArrow u V` maps cocontinuously to `D / V`; the
resulting square induces the stated direct-image comparison. -/
@[stacks 0D5R] #check @cocontinuousOverTopology.isContinuous

@[stacks 0D5R] #check @CostructuredArrow.CocontinuousOver.toOver_isCocontinuous

@[stacks 0D5R] #check @CostructuredArrow.CocontinuousOver.catCommSq

@[stacks 0D5R] #check @CostructuredArrow.CocontinuousOver.directImageComparison

end CategoryTheory
