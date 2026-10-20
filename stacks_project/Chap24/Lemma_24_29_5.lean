module

public import ReasLib.CategoryTheory.Adjunction.RightIso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.29.5 (tag 0FTT): after the corresponding left-adjoint composite is identified, uniqueness
of right adjoints gives the source's actual right-derived isomorphism.  The lower-level
`RightDerived.Composition.comparison` remains available for situations where no adjunction has
yet been constructed.
-/
@[stacks 0FTT] #check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso
#check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso_hom_counit
#check @CategoryTheory.Adjunction.rightAdjointIsoOfLeftIso_hom_app_counit
#check @CategoryTheory.Functor.RightDerived.Composition.comparison
#check @CategoryTheory.Functor.RightDerived.Composition.comparison_fac
#check @CategoryTheory.Functor.RightDerived.Cochain.functor
#check @CategoryTheory.Functor.RightDerived.Cochain.unit
