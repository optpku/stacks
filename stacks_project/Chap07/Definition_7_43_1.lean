module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
import StacksCheckRecall

@[expose] public section

/- Definition 7.43.1: for sites C and D, a morphism of topoi f : Sh(D) ⟶ Sh(C)
is an embedding exactly when the direct image f_* is fully faithful. This is
`MorphismOfTopoiIn.IsEmbedding`. -/
@[stacks 08LU] #check @CategoryTheory.MorphismOfTopoiIn.IsEmbedding

#check @CategoryTheory.LeftExactAdjunction.IsEmbedding
