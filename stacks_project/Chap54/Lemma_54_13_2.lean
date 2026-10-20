/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Normal
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 54.13.2: let `A` be a Noetherian local ring and let `B` and `C` be finite
`A`-algebras with an injective `A`-algebra homomorphism `B →ₐ[A] C`. If `B` is normal
and the completion of `C` along the extension of the maximal ideal of `A` is normal, then the
corresponding completion of `B` is normal. -/
@[stacks 0BGH] #check (IsNormalRing.adicCompletion_of_finite_injective :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (B : Type v) (C : Type w) [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C]
    (f : B →ₐ[A] C) (hf : Function.Injective f) [IsNormalRing B]
    [IsNormalRing
      (AdicCompletion (Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A)) C)],
    IsNormalRing
      (AdicCompletion (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B))
