module

public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.21.7

The two source clauses are componentwise consequences of the reusable
fully-faithful functor-of-sites API.
-/

@[expose] public section

/- Lemma 7.21.7 (00XT) (1): the unit of the continuous sheaf adjunction is
invertible for a fully faithful continuous and cocontinuous functor of sites. -/
@[stacks 00XT "(1)"] #check @CategoryTheory.Functor.sheafAdjunctionContinuous_unit_app_isIso_of_fullyFaithful

/- Lemma 7.21.7 (00XT) (2): the counit of the cocontinuous sheaf adjunction is
invertible for a fully faithful continuous and cocontinuous functor of sites. -/
@[stacks 00XT "(2)"] #check @CategoryTheory.Functor.sheafAdjunctionCocontinuous_counit_app_isIso_of_fullyFaithful
