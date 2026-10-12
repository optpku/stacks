/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finiteness detected on the residue field of an Artinian local ring

For a ring homomorphism with Artinian local target, finite, finite-type, and
essentially-finite-type behavior can all be detected after composing with the
residue map.  These are map-level criteria, so their canonical owner is the
`RingHom` namespace rather than a chosen composition series of the target.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace RingHom

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsArtinianRing S] [IsLocalRing S]

/-- A map to an Artinian local ring is finite exactly when its composition with the residue
map is finite. -/
@[stacks 07DT "(1)"]
theorem finite_iff_residue_finite (f : R →+* S) :
    f.Finite ↔ ((residue S).comp f).Finite := sorry

/-- A map to an Artinian local ring is of finite type exactly when its composition with the
residue map is of finite type. -/
@[stacks 07DT "(2)"]
theorem finiteType_iff_residue_finiteType (f : R →+* S) :
    f.FiniteType ↔ ((residue S).comp f).FiniteType := sorry

/-- A map to an Artinian local ring is essentially of finite type exactly when its composition
with the residue map is essentially of finite type. -/
@[stacks 07DT "(3)"]
theorem essFiniteType_iff_residue_essFiniteType (f : R →+* S) :
    f.EssFiniteType ↔ ((residue S).comp f).EssFiniteType := sorry

end RingHom
