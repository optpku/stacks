module

public import ReasLib.CategoryTheory.Sites.Descent.TypeSheaf
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.26.4

Effective descent for localized `Type`-valued sheaves is owned by the reusable
stack API. The former construction-specific glueing files remain historical
proof support, but are no longer part of this lemma's public import path.
-/

@[expose] public section

/- Lemma 7.26.4 (04TR): for every cover of `U`, the descent-data functor from
sheaves on `C / U` is essentially surjective. The canonical stronger owner is
that the localized sheaf pseudofunctor is a stack. -/
@[stacks 04TR] #check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.toDescentData_essSurj

@[stacks 04TR] #check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.isStackFor_cover

@[stacks 04TR] #check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.isStack
