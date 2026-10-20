/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.FormallySmooth.Criteria
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.138.8 (Tag 031J)

This is a canonical recall of the presentation-independent formal-smoothness
criteria.  `Algebra.Extension.HasInfinitesimalSection` and
`Algebra.Extension.HasConormalRetraction` keep the two presentation clauses
available as reusable predicates.

@stack 031J
-/

#check @Algebra.Extension.HasInfinitesimalSection
#check @Algebra.Extension.HasConormalRetraction

/- Proposition 10.138.8 (Tag 031J): the six formal-smoothness, presentation, and cotangent
criteria are equivalent. -/
@[stacks 031J]
#check @Algebra.FormallySmooth.Criteria.tfae
