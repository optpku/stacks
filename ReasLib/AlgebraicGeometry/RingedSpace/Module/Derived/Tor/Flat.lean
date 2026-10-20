/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat modules and Tor

This leaf owns the ringed-space flatness criterion for the source-facing two-variable Tor object.
It deliberately exports theorem companions rather than a global `IsZero` instance: Tor vanishing is
a consequence to invoke, not canonical structure to make typeclass search reconstruct.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Tor

variable {X : RingedSpace.{u}}
variable [Tensor.Has X]

/-- Lemma 20.26.16: a module sheaf is flat exactly when its first Tor with every module sheaf
vanishes. -/
@[stacks 08BQ]
theorem isFlat_iff_isZero_tor_one (F : Modules X) :
    F.IsFlat ↔ ∀ G : Modules X, IsZero (ModuleDerived.tor 1 F G) := sorry

/-- A flat module sheaf has vanishing first Tor with every module sheaf. -/
@[stacks 08BQ "flat modules have vanishing first Tor"]
theorem isZero_tor_one_of_isFlat (F : Modules X) (hF : F.IsFlat) (G : Modules X) :
    IsZero (ModuleDerived.tor 1 F G) := sorry

/-- Vanishing of first Tor against every module sheaf detects flatness. -/
@[stacks 08BQ "first Tor detects flatness"]
theorem isFlat_of_isZero_tor_one
    (F : Modules X) (hTor : ∀ G : Modules X, IsZero (ModuleDerived.tor 1 F G)) :
    F.IsFlat := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Tor

end
