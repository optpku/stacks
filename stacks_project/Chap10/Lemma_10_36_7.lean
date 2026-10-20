/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.36.7

@stack 00GO
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.7: for a ring homomorphism `R → S`, the elements of `S` that are integral over
`R` form an `R`-subalgebra of `S`. In mathlib this canonical subalgebra is `integralClosure R S`.
-/
@[stacks 00GO "integral closure subalgebra"]
#check @integralClosure

/- Companion recall: membership in `integralClosure R S` is exactly integrality over `R`. This is
the single-step bridge from the source set-theoretic phrasing to the canonical subalgebra API. -/
@[stacks 00GO "membership characterization"]
#check @mem_integralClosure_iff
