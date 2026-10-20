/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tor-amplitude closure under derived tensor

This is the ringed-space specialization of the interval-valued Tor-amplitude predicate.  The
fixed-right derived tensor gate is explicit, so downstream statements do not rebuild a monoidal
model or a chosen resolution.
-/

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [DerivedCategory.DerivedTensor.Right.Has (C := Modules X)]

/-- Stacks 09J4: Tor-amplitude intervals add under the canonical derived tensor product. -/
@[stacks 09J4 "ringed-space Tor-amplitude tensor closure"]
theorem HasTorAmplitudeIn.tensor
    {K L : ModuleDerived X} {a b c d : ℤ}
    (hK : HasTorAmplitudeIn K a b) (hL : HasTorAmplitudeIn L c d) :
    HasTorAmplitudeIn (K ⊗ᴸ L) (a + c) (b + d) := sorry

end AlgebraicGeometry.RingedSpace

end
