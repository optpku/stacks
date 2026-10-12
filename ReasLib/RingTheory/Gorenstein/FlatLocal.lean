/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.RingTheory.RingHom.Fiber.Quotient

@[expose] public section

universe u v

namespace IsGorensteinLocalRing

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

/-- For a flat local homomorphism of Noetherian local rings, the target is
Gorenstein exactly when the source and canonical closed fiber are Gorenstein. -/
theorem target_iff_source_and_closedFiber :
    IsGorensteinLocalRing B ↔
      IsGorensteinLocalRing A ∧
        IsGorensteinLocalRing ((IsLocalRing.maximalIdeal A).Fiber B) := sorry

end IsGorensteinLocalRing
