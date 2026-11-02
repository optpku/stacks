/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Triangulated Domains of Definition for Derived Functors

This source entry is a thin bridge to the source-defined (essential-constancy) derived-value API in
ReasLib.
The implementation deliberately exposes no chapter-local localization system, notation, or
instance construction.
-/

namespace CategoryTheory

/- Proposition 13.14.8: for an exact functor in a triangulated localization situation, the
objects where the right or left derived indexing diagram is essentially constant form a strictly full
triangulated subcategory.  The induced functor and its restricted localization factorization are
respectively triangulated and shift-compatible. -/
@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.triangulated

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.triangulated

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.functor.isTriangulated

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.functor.isTriangulated

/- The derived-domain functors and their localization factors are the reusable downstream
construction, rather than source-local `RF`/`LF` notation. -/
@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.functor.isInvertedBy

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.functor.isInvertedBy

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.functor

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.functor

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.functor.obj

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.functor.map

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.functor.obj

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.functor.map

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.functor.commShift

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.functor.commShift

@[stacks 05SE]
#check @fullSubcategoryLocalizerMorphism.invariance.isLocalizedFullyFaithful

@[stacks 05SE] #check @LocalizerMorphism.fullyFaithfulLocalizedFunctor

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.localizationFactorization

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.localizationFactorization

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.facIso

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.localizationFactorization.map_Q

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.facIso

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.localizationFactorization.map_Q

@[stacks 05SE] #check @Localization.Lifting.map_localization

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.zero

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.zero

@[stacks 05SE]
#check @Functor.RightDerived.DefinedAt.localizationFactorization.commShift

@[stacks 05SE] #check @Functor.RightDerived.DefinedAt.facIso.homCommShift

@[stacks 05SE]
#check @Functor.LeftDerived.DefinedAt.localizationFactorization.commShift

@[stacks 05SE] #check @Functor.LeftDerived.DefinedAt.facIso.homCommShift

@[stacks 05SE] #check @NatTrans.shift_app_comm

@[stacks 05SE]
#check @Functor.RightDerived.DefinedAt.localizationFactorization.isTriangulated

@[stacks 05SE]
#check @Functor.LeftDerived.DefinedAt.localizationFactorization.isTriangulated

end CategoryTheory
