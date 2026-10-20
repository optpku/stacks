/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Depth

@[expose] public section

universe u v

namespace RingHom.Flat.Local

/-- A flat local homomorphism of Noetherian local rings does not decrease ring depth. -/
theorem moduleDepth_le {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.Flat) :
    moduleDepth A A ≤ moduleDepth B B := sorry

end RingHom.Flat.Local
