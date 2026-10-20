/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.28.4 (tag 0FTI): the composite of two derived pullback functors is canonically
isomorphic to the derived pullback of the underived composite.  This is the homotopy-category
specialization `Functor.LeftDerived.Homotopy.Composition.iso`; its counit and componentwise
counit formulas characterize the comparison without exposing choices of total derived functors.
-/
@[stacks 0FTI] #check @CategoryTheory.Functor.LeftDerived.Homotopy.Composition.iso
#check @CategoryTheory.Functor.LeftDerived.Homotopy.Composition.counit
#check @CategoryTheory.Functor.LeftDerived.Homotopy.Composition.iso_hom_counit
#check @CategoryTheory.Functor.LeftDerived.Homotopy.Composition.iso_hom_counit_app
