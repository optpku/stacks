/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.IdealDepth
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.11.4: the `I`-depth of a finite Cohen–Macaulay module is the
   difference between its support dimension and that of its quotient by `IM`. -/
@[stacks 0BUX] #check
  (Module.CohenMacaulay.idealDepth_eq_supportDim_sub_quotient :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]
      (I : Ideal R) (hI : I ≠ ⊤),
      .some (I.depth M) = WithBot.map₂ (fun d e ↦ d - e) (Module.supportDim R M)
        (Module.supportDim R (M ⧸ (I • (⊤ : Submodule R M)))))
