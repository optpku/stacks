/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regularity Descent Along Faithfully Flat Maps

@stack 07NG

This leaf owns the descent of mathlib's global regular-ring predicate along
an explicit faithfully flat homomorphism.
-/

@[expose] public section

namespace RingHom.FaithfullyFlat

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.164.4, tag `07NG`: regularity descends along a faithfully flat
ring homomorphism. -/
@[stacks 07NG]
theorem isRegularRing {f : R →+* S} (hff : f.FaithfullyFlat) [IsRegularRing S] :
    IsRegularRing R := sorry

end RingHom.FaithfullyFlat
