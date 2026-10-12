/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reducedness Descent Along Faithfully Flat Maps

This leaf records the ring-level reducedness descent theorem independently of
any particular algebra presentation of the map.
-/

@[expose] public section

namespace RingHom.FaithfullyFlat

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Reducedness descends along a faithfully flat ring homomorphism. -/
@[stacks 033F]
theorem isReduced {f : R →+* S} (hff : f.FaithfullyFlat) [IsReduced S] :
    IsReduced R := sorry

end RingHom.FaithfullyFlat
