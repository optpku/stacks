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
# Compatibility Import for Eventual Ranges

The reusable additive and module-valued eventual-range API is owned by
`ReasLib.CategoryTheory.InverseSystem.EventualRange`.

@stack 0595
-/

/- Definition 10.86.1 (Stacks 0595): an inverse system is Mittag-Leffler when
the images into every fixed stage eventually stabilize.  Mathlib owns the
predicate; ReasLib adds structured eventual-range models for additive groups
and modules. -/
@[stacks 0595]
#check @CategoryTheory.Functor.IsMittagLeffler
@[stacks 0595 "eventual-range characterization"]
#check @CategoryTheory.Functor.isMittagLeffler_iff_eventualRange
@[stacks 0595 "range-containment characterization"]
#check @CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp
@[stacks 0595 "additive eventual range"]
#check @CategoryTheory.Functor.eventualRangeAddSubgroup
@[stacks 0595 "stable image"]
#check @CategoryTheory.Functor.stableImage
