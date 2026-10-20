/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Depth
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.62.8: a flat local homomorphism `f : A →+* B` of local Noetherian
rings does not decrease ring depth. Equivalently, if `moduleDepth A A = k` then
`k ≤ moduleDepth B B`. -/
@[stacks 0FWS] #check (RingHom.Flat.Local.moduleDepth_le :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f], f.Flat → moduleDepth A A ≤ moduleDepth B B)
