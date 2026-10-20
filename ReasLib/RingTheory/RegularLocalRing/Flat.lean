/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Noetherian

/-!
# Regular Local Rings Along Flat Local Homomorphisms

@stack 00OF

This leaf owns descent of regular-locality along flat local homomorphisms.
It is separate from `RegularLocalRing.Flatness`, whose purpose is the converse
criterion obtained from regular systems of parameters.
-/

@[expose] public section

universe u v

namespace RingHom.Flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A flat local homomorphism with regular-local target has regular-local source. -/
@[stacks 00OF "regular-local descent along a flat local ring homomorphism"]
theorem isRegularLocalRing_of_isLocalHom
    {f : R →+* S} [IsLocalHom f] (h_flat : f.Flat) [IsRegularLocalRing S] :
    IsRegularLocalRing R := sorry

end RingHom.Flat

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R]

/-- A flat local algebra map with regular-local target has regular-local source. -/
@[stacks 00OF]
theorem of_flat_localHom_of_regularTarget
    (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] [IsRegularLocalRing S] :
    IsRegularLocalRing R := sorry

end IsRegularLocalRing
