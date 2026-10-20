module

public import StacksCheckRecall.CommandCrossRef

-- The induced topos morphism is a reusable site-theoretic construction.
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
import StacksCheckRecall

@[expose] public section

/- Lemma 7.21.1 (00XO): a cocontinuous functor of sites induces a morphism of topoi whose direct
image is cocontinuous pushforward and whose inverse image is sheafified pullback. ReasLib owns
the construction and its projection API. -/
@[stacks 00XO] #check @CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous

#check @CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_pushforward
#check @CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_inverseImage
#check @CategoryTheory.Functor.morphismOfTopoiInOfCocontinuous_spec
