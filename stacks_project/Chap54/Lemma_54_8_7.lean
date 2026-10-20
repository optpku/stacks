/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.RationalSingularity
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 54.8.7: A Nagata regular local commutative ring of Krull dimension two defines
a rational singularity. -/
@[stacks 0B4Q] #check (IsRationalSingularity.ofRegularLocalRing :
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] [NagataRing A],
    ringKrullDim A = 2 → IsRationalSingularity A)
