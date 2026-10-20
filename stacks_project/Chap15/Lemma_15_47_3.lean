/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Regular.JRing.Quotient
import StacksCheckRecall

/-!
# Lemma 15.47.3

@stack 07P9
-/

@[expose] public section

/-! # Lemma 15.47.3: J-1 from J-0 prime quotients -/

/- Lemma 15.47.3, tag `07P9`: prime quotients that are `J-0` force the ring to be `J-1`. -/
@[stacks 07P9 "J-1 from J-0 prime quotients"]
#check @IsJ1Ring.of_primeQuotient_isJ0
