/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.DirectSum
import StacksCheckRecall

@[expose] public section

open scoped DirectSum

universe u v

/- Lemma 38.8.1 (1): for a Noetherian ring complete along `I`, the `I`-adic completion
of the direct sum of copies of `R` indexed by `A` is flat over `R`. -/
@[stacks 05DJ] #check
  (@Module.Flat.adicCompletionDirectSum :
    ∀ {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
      [IsAdicComplete I R] (A : Type v),
      Module.Flat R (AdicCompletion I (⨁ _ : A, R)))

/- Lemma 38.8.1 (2): for a Noetherian ring complete along `I`, the `I`-adic completion
of the direct sum of copies of `R` indexed by `A` is Mittag-Leffler over `R`. -/
@[stacks 05DJ] #check
  (@Module.MittagLeffler.adicCompletionDirectSum :
    ∀ {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing R]
      [IsAdicComplete I R] (A : Type v),
      Module.MittagLeffler R (AdicCompletion I (⨁ _ : A, R)))
