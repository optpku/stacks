module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous

/-!
# Lemma 7.41.2

Continuous direct image along a cocontinuous functor of sites preserves the local-surjectivity
formulation of surjectivity for `Type`-valued sheaves. The reusable API belongs to the topos owner
rather than this source index.
-/

@[expose] public section

/- Lemma 7.41.2 (04D7): the canonical continuous/cocontinuous direct-image API preserves local
surjectivity of `Type`-valued sheaf morphisms. -/
@[stacks 04D7] #check
  @CategoryTheory.Functor.SheafPushforwardContinuous.preservesLocallySurjective

/- The companion instance exposes the same result in the categorical `Epi` form needed by
downstream functorial arguments. -/
#check @CategoryTheory.Functor.SheafPushforwardContinuous.preservesEpimorphisms
