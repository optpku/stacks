/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
import StacksCheckRecall

@[expose] public section

/- Lemma 13.20.1 is the reusable bounded K-injective computation result and
its degree-zero injective specialization. -/
@[stacks 05TH] #check
  @CategoryTheory.Functor.KInjective.Bounded.computesAtOfInjectivePlus
@[stacks 05TH] #check @CategoryTheory.Functor.RightAcyclic.Bounded.of_injective
@[stacks 05TH] #check @CategoryTheory.Functor.RightAcyclic.of_injective

end
