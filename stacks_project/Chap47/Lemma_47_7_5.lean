/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.MatlisDuality.Completion
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.7.5: For a Noetherian local ring `R` and an injective hull `E` of its
residue field, the canonical action identifies the maximal-ideal-adic completion of
`R` with `Module.End R E`. -/
@[stacks 08Z6] #check
  (LinearMap.IsInjectiveHull.completionToEnd_bijective :
    ∀ (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull),
      Function.Bijective
        (Module.IsIdealPowerTorsion.completionToEnd (IsLocalRing.maximalIdeal R)
          (LinearMap.IsInjectiveHull.maximalIdealPowerTorsion R E ι hι)))
