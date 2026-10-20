/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived
import StacksCheckRecall

@[expose] public section

/- Definition 13.16.2 is owned by the reusable bounded-below right-derived
functor API.  The source notation `R^iF` is represented by the canonical
`RightDerived.Bounded.functor` and `RightDerived.Bounded.degree`; its degree-zero
comparison is `RightDerived.Bounded.zero`, constructed from the canonical
localization `unit`. -/
@[stacks 015A] #check @CategoryTheory.Functor.RightDerived.Bounded.functor
@[stacks 015A] #check @CategoryTheory.Functor.RightDerived.Bounded.unit
@[stacks 015A] #check @CategoryTheory.Functor.RightDerived.Bounded.degree
@[stacks 015A] #check @CategoryTheory.Functor.RightDerived.Bounded.zero
@[stacks 015A] #check @CategoryTheory.Functor.RightDerived.Bounded.Vanishes.inDegree
@[stacks 015A] #check @CategoryTheory.Functor.toBoundedBelowDerived.singleIso
#check @CategoryTheory.DerivedCategory.Plus.singleFunctor.fromHomotopy.iso

end
