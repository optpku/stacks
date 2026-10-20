/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived
import StacksCheckRecall

@[expose] public section

/- Lemma 13.16.6 is owned by the reusable construction of the cohomological
delta functor associated to a bounded-below right derived functor. -/
@[stacks 05TE] #check @CategoryTheory.DerivedCategory.Plus.singleFunctor.delta
@[stacks 05TE] #check @CategoryTheory.DerivedCategory.Plus.singleFunctor.fromHomotopy.iso
@[stacks 05TE] #check @CategoryTheory.Functor.RightDerived.delta
@[stacks 05TE] #check @CategoryTheory.Functor.RightDerived.delta_hneg
@[stacks 05TE] #check @CategoryTheory.Functor.RightDerived.cohomological
@[stacks 05TE] #check @CategoryTheory.Functor.RightDerived.cohomological_obj

end
