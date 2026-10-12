/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski
public import ReasLib.RingTheory.RingHom.Local.Properties

/-!
# Ind-Zariski local rings

An ind-Zariski ring homomorphism induces an isomorphism on every target local
ring.
-/

@[expose] public section

universe u

namespace RingHom.IndZariski

/-- An ind-Zariski ring homomorphism induces an isomorphism on every target
local ring. -/
theorem isIsoOnLocalRings {R A : Type u} [CommRing R] [CommRing A]
    {f : R →+* A} (hf : f.IndZariski) : f.IsIsoOnLocalRings :=
  sorry

end RingHom.IndZariski
