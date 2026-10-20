/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Compact.Generators
import StacksCheckRecall

@[expose] public section

/- Lemma 21.52.1 (094B): the canonical object-property form uses a separating family of compact
objects and records finite sums through `ObjectProperty.additiveClosure`. -/
@[stacks 094B]
#check @CategoryTheory.IsCompactObject.exists_retract_bounded_additiveClosure

#check @CategoryTheory.ObjectProperty.IsSeparating
#check @CategoryTheory.ObjectProperty.additiveClosure
#check @CochainComplex.Bounded
#check @CategoryTheory.Retract
