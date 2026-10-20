/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.FirstOrder
import StacksCheckRecall

/-!
# Universal First-Order Thickenings

The reusable predicate and the canonical square-zero-kernel comparison are
owned by `ReasLib.RingTheory.Extension.FirstOrder`.  The conormal module is
Mathlib's `Extension.Cotangent`, rather than a second proof-indexed carrier.

@stack 04EC
-/

@[expose] public section

/- Definition 10.149.2 (1): a universal first-order thickening is initial for
lifts against square-zero quotients. -/
@[stacks 04EC "(1), universal first-order thickening"]
#check @Algebra.Extension.FirstOrder.IsUniversal

@[stacks 04EC "(1), square-zero kernel"]
#check @Algebra.Extension.FirstOrder.IsUniversal.squareZero

@[stacks 04EC "(1), unique lift in the testing universe"]
#check @Algebra.Extension.FirstOrder.IsUniversal.existsUniqueLiftAt

@[stacks 04EC "(1), unique lift after universe lifting"]
#check @Algebra.Extension.FirstOrder.IsUniversal.existsUniqueLift

/- Definition 10.149.2 (2): for a square-zero thickening, the kernel presents
the canonical conormal/cotangent module. -/
@[stacks 04EC "(2), conormal module"]
#check @Algebra.Extension.kerCotangentEquiv

@[stacks 04EC "(2), canonical cotangent carrier"]
#check @Algebra.Extension.Cotangent

@[stacks 04EC "(2), kernel-to-cotangent comparison"]
#check @Algebra.Extension.kerCotangentEquiv_apply
