module

public import ReasLib.RingTheory.Normal.Ring
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Normal Local Rings

For a local commutative ring, the localization-based normality owner is equivalent to the familiar
domain and integrally-closed conditions.  The local-domain consequence is registered as an
instance so downstream localization arguments do not rebuild it with `letI`.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

namespace IsNormalRing

/-- A normal local ring is a domain and is integrally closed. -/
@[stacks 031S "normal local ring characterization"]
theorem local_iff [IsLocalRing R] :
    IsNormalRing R ↔ IsDomain R ∧ IsIntegrallyClosed R := sorry

end IsNormalRing

/-- Normality forces a local ring to be a domain. -/
@[stacks 031S "normal local ring domain instance"]
instance IsNormalRing.instIsDomain_of_isLocalRing [IsLocalRing R] [IsNormalRing R] :
    IsDomain R := sorry
