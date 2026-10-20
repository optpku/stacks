/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.Point.ActionDirectImage

/-!
# Example 7.33.7

The canonical forgetful point of the jointly-surjective action site and its direct-image formulas
are owned by the reusable `Action.ForgetfulPoint` namespace. This chapter entry is a source-facing
recall of the five assertions of the example.
-/

@[expose] public section

/- Example 7.33.7 (00YF) (1): the forgetful functor on `G`-sets defines a point of the
jointly-surjective action site. -/
@[stacks 00YF "(1)"] #check @Action.forgetfulPoint

/- Example 7.33.7 (00YF) (2): the inverse image of the direct image of `S` is canonically
the function type `G → S`. -/
@[stacks 00YF "(2)"] #check @Action.ForgetfulPoint.pushforwardFiberEquiv

/- Example 7.33.7 (00YF) (3): after the left-regular-sections equivalence, direct image is
the named right-translation action on `G → S`. -/
@[stacks 00YF "(3)"] #check @Action.ForgetfulPoint.pushforwardRightTranslationIso

/- Example 7.33.7 (00YF) (4): the section of the direct-image counit is the
constant-function map under the fiber equivalence. -/
@[stacks 00YF "(4)"] #check @Action.ForgetfulPoint.pushforwardFiber_section_eq_const

/- Example 7.33.7 (00YF) (5): the direct-image counit is evaluation at `1 ∈ G` under the
fiber equivalence. -/
@[stacks 00YF "(5)"] #check @Action.ForgetfulPoint.pushforwardFiber_counit_eq_eval_one
