/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex
import StacksCheckRecall

@[expose] public section

/-!
@stack 00MA

# Completion of finite modules over a Noetherian ring
-/

/- Lemma 10.97.1 (1): completion preserves injectivity for maps into finite modules over a
Noetherian ring. -/
@[stacks 00MA]
#check @AdicCompletion.map_injective

/- Lemma 10.97.1 (2) [stacks 00MA]: the short complex obtained by applying `AdicCompletion I`
to a short exact sequence with finite middle term is short exact. -/
@[stacks 00MA]
#check @AdicCompletion.mapShortComplex
#check @AdicCompletion.mapShortComplex_shortExact_of_finite

/- Lemma 10.97.1 (3): the canonical tensor comparison identifies the completion of a finite
module over a Noetherian ring. -/
@[stacks 00MA]
#check @AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
