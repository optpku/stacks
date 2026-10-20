module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
import StacksCheckRecall

@[expose] public section

/- Lemma 7.31.1 (04H1): localizing a morphism of topoi at a target sheaf is the specialization of
the slice localization of a left-exact adjunction. The generic ReasLib owner supplies the
objectwise inverse-image formula and the pushforward/restriction comparison. -/
@[stacks 04H1 "(1)"] #check @CategoryTheory.LeftExactAdjunction.localization_inverseImage_obj

@[stacks 04H1 "(2)"] #check @CategoryTheory.LeftExactAdjunction.localization_pushforwardStarIso

#check @CategoryTheory.LeftExactAdjunction.localization
