/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Basis
import StacksCheckRecall

/-!
# Equation 25.12.2.1

The chosen family in the source is represented by a fixed-target formal coproduct satisfying the
canonical basis-covering predicate: its generated sieve covers and every source lies in the
chosen collection.
-/

/- Equation 25.12.2.1: a chosen family covering a matching object and having all source objects
in the prescribed basis is a `FormalCoproduct.IsBasisCovering`. -/
@[stacks 0DAW]
#check @CategoryTheory.Limits.FormalCoproduct.IsBasisCovering

/- The indexed-arrow presentation recovers the displayed family and both of its source
conditions. -/
#check @CategoryTheory.Limits.FormalCoproduct.ofArrows_isBasisCovering_toPrecoverage_iff
