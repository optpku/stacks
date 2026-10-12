/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Nakayama
public import ReasLib.RingTheory.RingHom.FiniteType.Quotient

/-!
# Finite-Type Ring Maps Across Nilpotent Quotients

This leaf is the map-first finite-type lifting theorem for a nilpotent ideal.
It keeps the nilpotence hypothesis explicit rather than installing a global
instance, since the result is a reusable theorem about one chosen quotient.
-/

@[expose] public section

universe u v

namespace RingHom.FiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Tag `0G8U`: a ring map is finite type when its quotient by a nilpotent
source ideal and the corresponding target ideal is finite type. -/
@[stacks 0G8U "finite type across a nilpotent quotient"]
theorem of_quotient_nilpotent {f : R →+* S} {I : Ideal R} (hI : IsNilpotent I)
    (hquot : (f.quotientByIdeal I).FiniteType) :
    f.FiniteType := sorry

end RingHom.FiniteType

namespace Algebra.FiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Algebra-specialized finite-type lifting across a nilpotent quotient.  This
companion consumes the canonical quotient-algebra instance directly. -/
@[stacks 0G8U "finite-type algebra across a nilpotent quotient"]
theorem of_quotient_nilpotent (I : Ideal R) (hI : IsNilpotent I)
    [Algebra.FiniteType (R ⧸ I) (S ⧸ I.map (algebraMap R S))] :
    Algebra.FiniteType R S := sorry

end Algebra.FiniteType
