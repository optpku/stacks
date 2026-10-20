/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.QuotSMulTop

universe u v w

/- Theorem 41.9.2: let `A → B` be a local homomorphism of Noetherian local rings.
If the finite `B`-module `M` is flat over `A`, and multiplication by
`t ∈ IsLocalRing.maximalIdeal B` is injective on
`M ⧸ IsLocalRing.maximalIdeal A • ⊤`, then `M / tM` is flat over `A`. -/
@[stacks 0252] #check
  (Module.Flat.quotSMulTop_of_mod_maximalIdeal_injective :
    ∀ {A : Type u} {B : Type v} {M : Type w}
      [CommRing A] [CommRing B] [Algebra A B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      [IsLocalHom (algebraMap A B)]
      [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
      [Module.Finite B M] [Module.Flat A M]
      (t : B) (ht : t ∈ IsLocalRing.maximalIdeal B)
      (hmod : Function.Injective
        (((LinearMap.lsmul B M t).restrictScalars A).quotientMapByIdeal
          (IsLocalRing.maximalIdeal A))),
      Module.Flat A (QuotSMulTop t M))
