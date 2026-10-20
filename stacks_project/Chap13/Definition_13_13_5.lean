/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Quotient
import StacksCheckRecall

@[expose] public section

/- Definition 13.13.5 (`05S2`): the finite filtered derived category and its quotient functor are
the canonical localization owners in `Filtration/Derived/Quotient`. -/
@[stacks 05S2] #check @CategoryTheory.FilteredObject.FiniteDerived.Quotient.Category
@[stacks 05S2] #check @CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor
@[stacks 05S2] #check
  @CategoryTheory.FilteredObject.FiniteDerived.Quotient.isLocalization
