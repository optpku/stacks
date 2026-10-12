/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Quotient

/-!
# Finite-Type Ring Maps After Quotienting

This leaf records finite-type permanence for the map induced after quotienting
the source by an ideal and the target by its image.  The owner is map-first, so
it does not impose an ambient `Algebra` instance on consumers.
-/

@[expose] public section

universe u v

namespace RingHom.FiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Tag `0G8U`: quotienting a finite-type ring map by a source ideal preserves
finite type. -/
@[stacks 0G8U "finite-type quotient of a ring map"]
theorem quotientByIdeal {f : R →+* S} (hf : f.FiniteType) (I : Ideal R) :
    (f.quotientByIdeal I).FiniteType := sorry

end RingHom.FiniteType
