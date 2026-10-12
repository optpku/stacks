/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian Descent Along Faithfully Flat Maps

This leaf owns the ring-level Noetherian descent theorem for an explicit
faithfully flat homomorphism.
-/

@[expose] public section

namespace RingHom.FaithfullyFlat

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Noetherianity descends along a faithfully flat ring homomorphism. -/
@[stacks 033E]
theorem isNoetherianRing {f : R →+* S} (hff : f.FaithfullyFlat) [IsNoetherianRing S] :
    IsNoetherianRing R := sorry

end RingHom.FaithfullyFlat
