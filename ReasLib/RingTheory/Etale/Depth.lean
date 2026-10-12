/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.LocalRing
public import ReasLib.RingTheory.Flat.Fiber.Depth

@[expose] public section

namespace RingHom.Etale

universe u v

/-- An étale local homomorphism of Noetherian local rings preserves ring depth. -/
theorem moduleDepth_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f] (hf : f.Etale) :
    moduleDepth A A = moduleDepth B B := sorry

end RingHom.Etale
