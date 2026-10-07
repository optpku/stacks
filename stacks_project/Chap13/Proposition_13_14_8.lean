module

import ReasLib.CategoryTheory.Functor.Derived.Definedness
import StacksCheckRecall

@[expose] public section

/-!
# Triangulated Domains of Definition for Derived Functors

This source entry is a thin bridge to the general pointwise-derived definedness API in ReasLib.
The implementation deliberately exposes no chapter-local localization system, notation, or
instance construction.
-/

namespace CategoryTheory

/- Proposition 13.14.8: for an exact functor in a triangulated localization situation, the
objects where its pointwise right or left derived value is defined form a strictly full
triangulated subcategory.  The induced functor and its restricted localization factorization are
respectively exact and shift-compatible. -/
@[stacks 05SE] #check @Functor.RightDerived.Definedness.property.isTriangulated

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.property.isTriangulated

/- The derived-domain functors and their localization factors are the reusable downstream
construction, rather than source-local `RF`/`LF` notation. -/
@[stacks 05SE] #check @Functor.RightDerived.Definedness.valueMap.isIso_of_mem

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.valueMap.isIso_of_mem

@[stacks 05SE] #check @Functor.RightDerived.Definedness.functor.isInvertedBy

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.functor.isInvertedBy

@[stacks 05SE] #check @Functor.RightDerived.Definedness.functor

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.functor

@[stacks 05SE] #check @Functor.RightDerived.Definedness.functor.obj

@[stacks 05SE] #check @Functor.RightDerived.Definedness.functor.map

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.functor.obj

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.functor.map

@[stacks 05SE] #check @Functor.RightDerived.Definedness.functor.commShift

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.functor.commShift

@[stacks 05SE]
#check @fullSubcategoryLocalizerMorphism.invariance.isLocalizedFullyFaithful

@[stacks 05SE] #check @LocalizerMorphism.fullyFaithfulLocalizedFunctor

@[stacks 05SE] #check @Functor.RightDerived.Definedness.localizationFactorization

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.localizationFactorization

@[stacks 05SE] #check @Functor.RightDerived.Definedness.facIso

@[stacks 05SE] #check @Functor.RightDerived.Definedness.facIso.hom_naturality

@[stacks 05SE] #check @Functor.RightDerived.Definedness.facIso.inv_naturality

@[stacks 05SE] #check @Functor.RightDerived.Definedness.localizationFactorization.map_Q

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.facIso

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.facIso.hom_naturality

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.facIso.inv_naturality

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.localizationFactorization.map_Q

@[stacks 05SE] #check @Localization.Lifting.map_localization

@[stacks 05SE] #check @Functor.RightDerived.Definedness.property.zero

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.property.zero

@[stacks 05SE]
#check @Functor.RightDerived.Definedness.localizationFactorization.commShift

@[stacks 05SE]
#check @Functor.RightDerived.Definedness.localizationFactorization.commShiftIso_hom_app_Q

@[stacks 05SE]
#check @Functor.RightDerived.Definedness.localizationFactorization.commShiftIso_inv_app_Q

@[stacks 05SE] #check @Functor.RightDerived.Definedness.facIso.homCommShift

@[stacks 05SE]
#check @Functor.LeftDerived.Definedness.localizationFactorization.commShift

@[stacks 05SE]
#check @Functor.LeftDerived.Definedness.localizationFactorization.commShiftIso_hom_app_Q

@[stacks 05SE]
#check @Functor.LeftDerived.Definedness.localizationFactorization.commShiftIso_inv_app_Q

@[stacks 05SE] #check @Functor.LeftDerived.Definedness.facIso.homCommShift

@[stacks 05SE] #check @NatTrans.shift_app_comm

@[stacks 05SE]
#check @Functor.RightDerived.Definedness.localizationFactorization.isTriangulated

@[stacks 05SE]
#check @Functor.LeftDerived.Definedness.localizationFactorization.isTriangulated

end CategoryTheory
