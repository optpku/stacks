/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.29.4: the derived pullback/direct-image adjunction is the canonical derived adjunction
`Adjunction.derived`.  Its Hom-set equivalence is the existing `Adjunction.homEquiv`; the
left/right derived functors and their comparison maps are exposed by the generic cochain owners.
-/
@[stacks 0FTR] #check @CategoryTheory.Adjunction.derived
#check @CategoryTheory.Adjunction.homEquiv
#check @CategoryTheory.Functor.LeftDerived.Homotopy.functor
#check @CategoryTheory.Functor.LeftDerived.Homotopy.counit
#check @CategoryTheory.Functor.RightDerived.Cochain.functor
#check @CategoryTheory.Functor.RightDerived.Cochain.unit
