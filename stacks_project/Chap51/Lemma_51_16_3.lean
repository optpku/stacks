/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.LocalCohomology.Surjectivity
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.16.3: if `f` avoids every top-dimensional minimal prime of a
Noetherian local ring `A` of dimension `d`, then multiplication by `f` is
surjective on degree-`d` local cohomology for every finite `A`-module and every
ideal of support. -/
@[stacks 0EB3] #check
  (localCohomology.smul_surjective_of_notMem_topDim :
    ∀ {A M : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (d : ℕ) (hdim : ringKrullDim A = d) (f : A)
      (h_notMem : ∀ p ∈ minimalPrimes.topDim A, f ∉ p) (I : Ideal A),
      Function.Surjective
        (LinearMap.lsmul A ((localCohomology I d).obj (ModuleCat.of A M)) f))
