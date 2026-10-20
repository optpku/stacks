/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.EventualRange
import StacksCheckRecall

@[expose] public section

/-!
# Surjective Models of Mittag-Leffler Systems

Mathlib's set-valued eventual-range functor is the canonical owner of Example
10.86.2.  The module-valued stable image in ReasLib is its structured algebraic
companion.

@stack 0596
-/

/- Example 10.86.2 (1), Stacks 0596: an inverse system whose transition maps
are surjective is Mittag-Leffler. -/
@[stacks 0596 "surjective systems are Mittag-Leffler"]
#check @CategoryTheory.Functor.isMittagLeffler_of_surjective

/- Example 10.86.2 (2), Stacks 0596: the transition maps between eventual
ranges of a Mittag-Leffler system are surjective. -/
@[stacks 0596 "surjective eventual-range replacement"]
#check @CategoryTheory.Functor.surjective_toEventualRanges

/- Example 10.86.2 (3), Stacks 0596: passing to eventual ranges does not
change the inverse limit, expressed as the type of compatible sections. -/
@[stacks 0596 "eventual-range sections equivalence"]
#check @CategoryTheory.Functor.toEventualRangesSectionsEquiv

#check @CategoryTheory.Functor.stableImage
#check @CategoryTheory.Functor.mem_stableImage_iff
