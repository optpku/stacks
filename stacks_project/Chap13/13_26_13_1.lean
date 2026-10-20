/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Finite.Compatibility
import StacksCheckRecall

@[expose] public section

/-!
# Equation 13.26.13.1

The source equation is the bounded-below homotopy functor induced by the reusable finite
filtration map functor.
-/

namespace CategoryTheory.FilteredComplex.RightDerived.Finite.LeftExact

/- Equation 13.26.13.1 (`05TZ`): a left-exact functor acts on bounded-below complexes of finite
filtered objects. -/
@[stacks 05TZ] #check @homotopy

end CategoryTheory.FilteredComplex.RightDerived.Finite.LeftExact
