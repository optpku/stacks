/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Specializing localizations

The `A`-algebra of points specializing to a standard locally closed stratum
`D(f) ∩ V(I)` is the localization of `A` at the preimage of the units of
`(A ⧸ I)_f`.
-/

@[expose] public section

universe u

namespace Algebra.WLocalHull

variable (A : Type u) [CommRing A]

/-- Sections of the structure sheaf on the standard locally closed stratum
`D(f) ∩ V(I)`, realized as the localization `(A ⧸ I)_f`. -/
abbrev stratumSections (f : A) (I : Ideal A) : Type u :=
  Localization.Away (Ideal.Quotient.mk I f)

/-- The structure map `A →+* (A ⧸ I)_f` through the quotient `A ⧸ I`. -/
def toStratumSections (f : A) (I : Ideal A) : A →+* stratumSections A f I :=
  (algebraMap (A ⧸ I) (stratumSections A f I)).comp (Ideal.Quotient.mk I)

/-- The multiplicative set of elements of `A` that become units on the
stratum `D(f) ∩ V(I)`. -/
def specializingSubmonoid (f : A) (I : Ideal A) : Submonoid A :=
  (IsUnit.submonoid (stratumSections A f I)).comap (toStratumSections A f I)

/-- The localization of `A` at the multiplicative set of functions invertible
on `D(f) ∩ V(I)`, i.e. the ring of points specializing to that stratum. -/
abbrev specializingLocalization (f : A) (I : Ideal A) : Type u :=
  Localization (specializingSubmonoid A f I)

/-- Membership in the specializing multiplicative set is invertibility on the
stratum. -/
theorem specializingSubmonoid_mem_iff (f : A) (I : Ideal A) {a : A} :
    a ∈ specializingSubmonoid A f I ↔ IsUnit (toStratumSections A f I a) :=
  sorry

end Algebra.WLocalHull
