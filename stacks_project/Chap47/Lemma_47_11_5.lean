/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Fiber.IdealDepth
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.11.5: if the closed fiber of a flat local map of Noetherian local
rings is Cohen–Macaulay, then the `I`-depth of the target is bounded below by
the difference between the dimensions of `S/(𝔪S)` and `S/(𝔪S + I)`. -/
@[stacks 0BUY] #check
  (Algebra.Fiber.depth_ge_closedFiberDim_sub_quotientDim :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
      [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
      [Module.CohenMacaulay ((IsLocalRing.maximalIdeal R).Fiber S)
        ((IsLocalRing.maximalIdeal R).Fiber S)] (I : Ideal S),
      .some (I.depth S) ≥
        WithBot.map₂ (fun d e ↦ d - e)
          (ringKrullDim
            (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)))
          (ringKrullDim
            (S ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ⊔ I))))
