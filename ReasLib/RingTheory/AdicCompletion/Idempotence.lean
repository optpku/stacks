/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.AlgebraMap
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Idempotence of adic completion -/

@[expose] public section

noncomputable section

universe u

namespace AdicCompletion

/-- If `B` is the `I`-adic completion of a Noetherian ring `A`, then the
canonical `extensionMap I` is bijective. -/
theorem bijective_extensionMap_adicCompletion {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    Function.Bijective
      (extensionMap I :
        AdicCompletion I A →+*
          AdicCompletion (I.map (algebraMap A (AdicCompletion I A)))
            (AdicCompletion I A)) :=
  sorry

end AdicCompletion
