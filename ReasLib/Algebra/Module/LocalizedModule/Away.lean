/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing detected by principal localization

This leaf isolates the elementary criterion that a module already vanishes
when its localization away from a regular element vanishes.

@stack 0H7N
-/

@[expose] public section

universe u v

namespace LocalizedModule.Away

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Stacks 0H7N: if localizing `M` away from `f` is subsingleton and `f` acts
injectively on `M`, then `M` is subsingleton. -/
@[stacks 0H7N "vanishing detected by principal localization"]
theorem subsingleton_of_isSMulRegular {f : R}
    (hf : IsSMulRegular M f) (hAway : Subsingleton (LocalizedModule.Away f M)) :
    Subsingleton M := sorry

end LocalizedModule.Away
