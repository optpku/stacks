/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.PresentationSequence

@[expose] public section

/- 16.3.1.2: adding the same free summand to the first two terms preserves the
exact conormal sequence and the surjectivity of its right map. -/
@[stacks 07EX]
#check @Algebra.Generators.Cotangent.exact_stabilized_postcomp_equiv
