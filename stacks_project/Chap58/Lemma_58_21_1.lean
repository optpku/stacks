/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.KrullDimension.HeightOne
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 58.21.1: Let `A` be a Noetherian local ring with positive Krull dimension.
For `f` in its maximal ideal, there is `p ∈ V(f)` such that the localization of `A` at
`p` has Krull dimension one. -/
@[stacks 0BJG] #check (IsLocalRing.exists_prime_mem_zeroLocus_singleton_dim_one :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A],
      1 ≤ ringKrullDim A →
        ∀ f : A, f ∈ IsLocalRing.maximalIdeal A →
          ∃ p : PrimeSpectrum A,
            p ∈ PrimeSpectrum.zeroLocus ({f} : Set A) ∧
              ringKrullDim (Localization.AtPrime p.asIdeal) = 1)
