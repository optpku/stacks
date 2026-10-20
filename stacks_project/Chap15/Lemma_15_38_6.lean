/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime.Adic
import StacksCheckRecall

/-!
# Lemma 15.38.6

@stack 07VH
-/

@[expose] public section

/- Lemma 15.38.6, tag `07VH`: for a finite-type algebra over a Noetherian ring, smoothness at
a prime is equivalent to adic formal smoothness of the induced map on local rings. -/
@[stacks 07VH]
#check @Algebra.smoothAtPrime_iff_formally_smooth_for_adic_localized_map
