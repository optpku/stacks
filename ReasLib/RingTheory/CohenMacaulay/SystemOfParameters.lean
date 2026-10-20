/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.RegularLocalRing.Parameters

@[expose] public section

open IsLocalRing RingTheory.Sequence

universe u

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A Noetherian local ring is Cohen–Macaulay of dimension `d` if and only if it admits
a system of parameters of length `d` whose ordered entries form a regular sequence. -/
@[stacks 0285]
theorem iff_exists_isSystemOfParameters_isRegular [IsNoetherianRing R] (d : ℕ) :
    Module.CohenMacaulay R R ∧ ringKrullDim R = d ↔
      ∃ x : Fin d → maximalIdeal R,
        IsSystemOfParameters x ∧ IsRegular R (List.ofFn fun i ↦ (x i : R)) := sorry

end Module.CohenMacaulay
