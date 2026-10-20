/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.28.3 (tag 0FTH): the left derived functor of a composite is compared with the
composite of the two left derived functors.  The reusable statement is the canonical natural
transformation `Functor.LeftDerived.Composition.comparison`; an equality of chosen functors is
not invariant under the choices made by the total-derived construction.  When the underived
composite is identified by an isomorphism, the homotopy-category specialization provides
`Functor.LeftDerived.Homotopy.Composition.iso` and its counit formulas.
-/
#check @CategoryTheory.Functor.LeftDerived.Composition.comparison
#check @CategoryTheory.Functor.LeftDerived.Composition.comparison_fac
@[stacks 0FTH "derived pullback followed by derived tensoring"]
#check @CategoryTheory.Functor.LeftDerived.Homotopy.Composition.iso
#check @CategoryTheory.Functor.LeftDerived.Homotopy.Composition.iso_hom_counit
#check @CategoryTheory.Functor.LeftDerived.Homotopy.Composition.iso_hom_counit_app
