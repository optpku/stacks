module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.Adjoint
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.22.1

The adjoint descriptions of cocontinuous direct and inverse image are owned
by ReasLib. This file keeps the textbook label and its two source-facing
presentations without creating a second API surface.
-/

@[expose] public section

/- Lemma 7.22.1 (00XX) (1): when `u` has right adjoint `v`, the underlying
presheaf of cocontinuous direct image along `u` is precomposition by `v.op`. -/
@[stacks 00XX "(1)"] #check @CategoryTheory.Functor.CocontinuousPushforward.rightAdjointIso

@[stacks 00XX "(1)"] #check @CategoryTheory.Functor.CocontinuousPushforward.rightAdjointIso_hom_app_isIso

/- Lemma 7.22.1 (00XX) (2): the cocontinuous inverse image is the
sheafification of the left Kan extension along `v.op`. -/
@[stacks 00XX "(2)"] #check @CategoryTheory.Functor.CocontinuousPullback.rightAdjointSheafifyLanIso

@[stacks 00XX "(2)"] #check @CategoryTheory.Functor.CocontinuousPullback.rightAdjointSheafifyLanIso_hom_isIso
