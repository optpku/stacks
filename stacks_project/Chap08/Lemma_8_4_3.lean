/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Stack
import StacksCheckRecall

@[expose] public section

/-!
# Full subcategories of stacks

The proof-only descent transport and cartesian-lift scaffolding for this item is owned by
`ReasLib.CategoryTheory.Fibered.FullSubcategory.Stack`.  The chapter entry is a direct recall of
that criterion, with the source's fiberwise hypotheses represented by
`ObjectProperty.IsStableUnder.CartesianPullback` and the choice-independent
`ObjectProperty.Fiberwise.IsLocal` API.
-/

namespace CategoryTheory

/- Lemma 8.4.3 (tag 04TU): a full subcategory of a stack remains a stack when its defining
property is stable under fiberwise cartesian pullback up to isomorphism and its fiberwise
iso-closure is local for the covering topology. -/
@[stacks 04TU "full subcategories of stacks"]
#check @ObjectProperty.FullSubcategory.isStackOnSite

#check @ObjectProperty.FullSubcategory.isFibered
#check @ObjectProperty.fiber
#check @ObjectProperty.IsStableUnder.CartesianPullback
#check @ObjectProperty.IsStableUnder.cartesianPullback_iff_pullback
#check @ObjectProperty.Fiberwise.IsLocal
#check @ObjectProperty.Fiberwise.IsLocal.iff_of_cleavage
#check @ObjectProperty.IsFiberwiseLocal
#check @ObjectProperty.IsFiberwiseLocal.iff_for

/- The reusable fiber comparison keeps both functors and the identity-owner unit and counit
explicit; later proofs need not transport an equivalence along functor equalities. -/
#check @ObjectProperty.Fiber.toFullSubcategory
#check @ObjectProperty.Fiber.fromFullSubcategory
#check @ObjectProperty.Fiber.unitApp
#check @ObjectProperty.Fiber.counitApp
#check @ObjectProperty.Fiber.equivalence

end CategoryTheory
