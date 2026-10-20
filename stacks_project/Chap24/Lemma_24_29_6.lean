module

public import ReasLib.CategoryTheory.Adjunction.RightIso
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.29.6: after identifying the left derived functor for a composite with the composite of
left derived functors, the corresponding right derived functors are canonically isomorphic.  The
neutral owner is `Adjunction.rightAdjointIsoOfLeftIso`; its counit equations are available without
unfolding the chosen derived-functor constructions.
-/
@[stacks 0FTU] #check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso
#check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso_hom_counit
#check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso_hom_app_counit
#check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso_symm
#check @CategoryTheory.Adjunction.rightAdjointUniq
#check @CategoryTheory.Adjunction.rightAdjointUniq_hom_counit
