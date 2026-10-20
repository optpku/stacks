/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module.Quotient
public import ReasLib.RingTheory.Depth.RegularSequence

/-!
# Regular-sequence extensions for Cohen--Macaulay modules

The canonical API is phrased with `Module.supportDim` and `moduleDepth`; a
natural-number dimension presentation is exposed separately as a thin
source-facing bridge.  This keeps downstream arguments independent of an
arbitrary choice of `d`.
-/

@[expose] public section

open RingTheory Sequence IsLocalRing
open scoped ENat Pointwise

universe u v

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If a maximal-ideal list has the expected support-dimension drop in a
Cohen--Macaulay module, it extends to a regular sequence realizing the module
depth.  The conclusion uses the canonical `moduleDepth` rather than an
auxiliary natural-number parameter.
-/
theorem exists_maximal_regular_extension_of_supportDim_quotient_add_length_eq
    [Module.CohenMacaulay R M] {gs : List R}
    (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    ∃ gs' : List R,
      IsRegular M (gs ++ gs') ∧ moduleDepth R M = (gs ++ gs').length := sorry

/-- The expected support-dimension drop already forces the given list to be
regular in a Cohen--Macaulay module.
-/
theorem isRegular_of_supportDim_quotient_add_length_eq
    [Module.CohenMacaulay R M] {gs : List R}
    (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    IsRegular M gs := sorry

/-- Proposition 10.103.4 (Stacks tag `00N6`): after a natural-number
presentation `supportDim R M = d`, the maximal regular extension has length
`d`.  This is the source-facing bridge for the canonical theorem above.
-/
@[stacks 00N6]
theorem exists_maximal_regular_extension_of_supportDim_quotient_add_length_eq_of_nat
    [Module.CohenMacaulay R M] {gs : List R} {d : ℕ}
    (hgs : ∀ g ∈ gs, g ∈ maximalIdeal R)
    (hMdim : Module.supportDim R M = d)
    (hquot :
      Module.supportDim R (M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))) + gs.length =
        Module.supportDim R M) :
    ∃ gs' : List R,
      IsRegular M (gs ++ gs') ∧ d = (gs ++ gs').length := sorry

end Module.CohenMacaulay
