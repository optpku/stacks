/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Injective.Characterizations

/-!
# Definition 15.55.1

@stack 0AVD
-/

@[expose] public section

/- Definition 15.55.1 (0AVD): an `R`-module is injective if and only if its contravariant
represented Hom functor is exact. -/
@[stacks 0AVD "injective modules and exact represented Hom"]
#check @Module.injective_iff_exact_preadditiveYonedaObj

#check @CategoryTheory.injective_iff_exact_preadditiveYonedaObj
#check @Module.injective_iff_injective_object
