module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tor-amplitude closure under derived tensor

This is the ringed-space specialization of the interval-valued Tor-amplitude predicate.  The
fixed-right derived tensor gate is explicit, so downstream statements do not rebuild a monoidal
model or a chosen resolution.
-/

open AlgebraicGeometry CategoryTheory
open scoped RingedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Stacks 09J4: Tor-amplitude intervals add under the canonical derived tensor product. -/
@[stacks 09J4 "ringed-space Tor-amplitude tensor closure"]
theorem HasTorAmplitudeIn.tensor
    {K L : ModuleDerived X} {a b c d : ℤ}
    (hK : HasTorAmplitudeIn K a b) (hL : HasTorAmplitudeIn L c d) :
    HasTorAmplitudeIn (K ⊗^L L) (a + c) (b + d) := sorry

end AlgebraicGeometry.RingedSpace

end
