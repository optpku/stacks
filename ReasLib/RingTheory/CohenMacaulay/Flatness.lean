/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module

/-!
# Miracle Flatness

This leaf owns the local miracle-flatness criterion for a Cohen--Macaulay
target over a regular local base, expressed through the closed-fiber
dimension formula.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace RingHom.Flat

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsRegularLocalRing R]
variable [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalHom (algebraMap R S)]

include S

/-- Stacks 00R4: a Cohen--Macaulay local algebra over a regular local ring is flat when its
dimension is the sum of the base and closed-fiber dimensions. -/
@[stacks 00R4 "miracle flatness"]
theorem of_cohenMacaulay_of_fiber_dim
    (hCM : Module.CohenMacaulay S S)
    (hdim : ringKrullDim S = ringKrullDim R + ringKrullDim (Ideal.Fiber (maximalIdeal R) S)) :
    (algebraMap R S).Flat := sorry

omit S

end RingHom.Flat
