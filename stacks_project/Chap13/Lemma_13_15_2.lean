/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt.Value
import StacksCheckRecall

@[expose] public section

/- Lemma 13.15.2 is owned by the bounded source-definedness and computation-comparison APIs.
Bare source-definedness gives the canonical bounded/unbounded value isomorphism; the stronger
`ComputesAt` layer records the identity-denominator computation clauses. -/
@[stacks 05T5] #check @CategoryTheory.Functor.RightDerived.DefinedAt.iff_boundedBelow
@[stacks 05T5] #check @CategoryTheory.Functor.RightDerived.DefinedAt.ofBoundedBelow
@[stacks 05T5] #check @CategoryTheory.Functor.RightDerived.Value.boundedBelowIso
@[stacks 05T5] #check @CategoryTheory.Functor.RightDerived.Value.boundedBelowIso.hom_naturality
@[stacks 05T5] #check @CategoryTheory.Functor.RightDerived.Value.boundedBelowIso.hom_ι
@[stacks 05T5] #check @CategoryTheory.Functor.RightDerived.Value.BoundedBelow.isoOfBounded
@[stacks 05T5] #check @CategoryTheory.Functor.RightDerived.ComputesAt.iff_boundedBelow
@[stacks 05T5] #check @CategoryTheory.Functor.RightDerived.ComputesAt.boundedBelowValueIso
@[stacks 05T5] #check @CategoryTheory.Functor.LeftDerived.DefinedAt.iff_boundedAbove
@[stacks 05T5] #check @CategoryTheory.Functor.LeftDerived.DefinedAt.ofBoundedAbove
@[stacks 05T5] #check @CategoryTheory.Functor.LeftDerived.Value.boundedAboveIso
@[stacks 05T5] #check @CategoryTheory.Functor.LeftDerived.Value.boundedAboveIso.hom_naturality
@[stacks 05T5] #check @CategoryTheory.Functor.LeftDerived.Value.boundedAboveIso.hom_π
@[stacks 05T5] #check @CategoryTheory.Functor.LeftDerived.Value.BoundedAbove.isoOfBounded
@[stacks 05T5] #check @CategoryTheory.Functor.LeftDerived.ComputesAt.iff_boundedAbove
@[stacks 05T5] #check @CategoryTheory.Functor.LeftDerived.ComputesAt.boundedAboveValueIso

end
