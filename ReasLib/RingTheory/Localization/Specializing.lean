/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Specializing localizations of affine locally closed strata

For a commutative ring `A`, an element `f : A`, and an ideal `I`, the standard
locally closed set `D(f) ∩ V(I)` has global sections `(A ⧸ I)_f`.  The
multiplicative set of elements of `A` that become units there yields the
`A`-algebra of points specializing to that stratum.
-/

@[expose] public section

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- The standard locally closed subset `D(f) ∩ V(I)` of `PrimeSpectrum A`. -/
def basicLocallyClosed (f : A) (I : Ideal A) : Set (PrimeSpectrum A) :=
  (basicOpen f : Set (PrimeSpectrum A)) ∩ zeroLocus (I : Set A)

/-- Membership in `D(f) ∩ V(I)`: `f` is nonvanishing and `I` is contained in
the prime. -/
theorem mem_basicLocallyClosed {f : A} {I : Ideal A} {p : PrimeSpectrum A} :
    p ∈ basicLocallyClosed f I ↔ f ∉ p.asIdeal ∧ I ≤ p.asIdeal :=
  sorry

/-- Each standard locally closed subset `D(f) ∩ V(I)` is locally closed. -/
theorem isLocallyClosed_basicLocallyClosed (f : A) (I : Ideal A) :
    IsLocallyClosed (basicLocallyClosed f I) :=
  sorry

/-- The set of points of `PrimeSpectrum A` that specialize to a point of `Z`. -/
def specializesTo (Z : Set (PrimeSpectrum A)) : Set (PrimeSpectrum A) :=
  {p | ∃ q ∈ Z, p ⤳ q}

/-- Membership in the set of points specializing to `Z`. -/
theorem mem_specializesTo {Z : Set (PrimeSpectrum A)} {p : PrimeSpectrum A} :
    p ∈ specializesTo Z ↔ ∃ q ∈ Z, p ⤳ q :=
  sorry

end PrimeSpectrum

namespace Localization

variable {A : Type u} [CommRing A]

/-- The canonical map `A →+* (A ⧸ I)_f` through the quotient `A ⧸ I`. -/
def toAwayQuotient (f : A) (I : Ideal A) :
    A →+* Localization.Away (Ideal.Quotient.mk I f) :=
  (algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))).comp
    (Ideal.Quotient.mk I)

/-- `toAwayQuotient` evaluates as the composite of `Ideal.Quotient.mk` with the
algebra map into `(A ⧸ I)_f`. -/
theorem toAwayQuotient_apply (f : A) (I : Ideal A) (a : A) :
    toAwayQuotient f I a =
      algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))
        (Ideal.Quotient.mk I a) :=
  rfl

/-- `toAwayQuotient` is the composite of `Ideal.Quotient.mk I` with the algebra
map of `Localization.Away (Ideal.Quotient.mk I f)`. -/
theorem toAwayQuotient_comp (f : A) (I : Ideal A) :
    toAwayQuotient f I =
      (algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))).comp
        (Ideal.Quotient.mk I) :=
  rfl

/-- The multiplicative set of elements of `A` that become units in
`(A ⧸ I)_f`. -/
def specializingSubmonoid (f : A) (I : Ideal A) : Submonoid A :=
  Submonoid.comap (toAwayQuotient f I)
    (IsUnit.submonoid (Localization.Away (Ideal.Quotient.mk I f)))

/-- Membership in the specializing multiplicative set is invertibility on
`(A ⧸ I)_f`. -/
theorem mem_specializingSubmonoid_iff (f : A) (I : Ideal A) {a : A} :
    a ∈ specializingSubmonoid f I ↔ IsUnit (toAwayQuotient f I a) :=
  Iff.rfl

/-- An element of `A` lies in the specializing multiplicative set if and only
if `D(f) ∩ V(I)` is contained in `D(a)`. -/
theorem mem_specializingSubmonoid_iff_subset_basicOpen (f : A) (I : Ideal A)
    {a : A} :
    a ∈ specializingSubmonoid f I ↔
      PrimeSpectrum.basicLocallyClosed f I ⊆ PrimeSpectrum.basicOpen a :=
  sorry

/-- The `A`-algebra of points specializing to `D(f) ∩ V(I)`, as the
localization of `A` at `specializingSubmonoid f I`. -/
abbrev specializing (f : A) (I : Ideal A) : Type u :=
  Localization (specializingSubmonoid f I)

/-- The specializing multiplicative set, and hence `specializing f I`, depends
only on the underlying locally closed subset `D(f) ∩ V(I)`. -/
theorem specializingSubmonoid_eq_of_basicLocallyClosed_eq {f g : A}
    {I J : Ideal A} (h : PrimeSpectrum.basicLocallyClosed f I =
      PrimeSpectrum.basicLocallyClosed g J) :
    specializingSubmonoid f I = specializingSubmonoid g J :=
  sorry

namespace Specializing

/-- The canonical surjection `specializing f I →+* (A ⧸ I)_f` induced by
`toAwayQuotient`. -/
noncomputable def toAwayQuotient (f : A) (I : Ideal A) :
    specializing f I →+* Localization.Away (Ideal.Quotient.mk I f) :=
  IsLocalization.lift (M := specializingSubmonoid f I)
    (g := Localization.toAwayQuotient f I) fun y ↦
      (IsUnit.mem_submonoid_iff _).mp (Submonoid.mem_comap.mp y.property)

/-- The canonical surjection from `specializing f I` extends
`Localization.toAwayQuotient`. -/
theorem toAwayQuotient_comp (f : A) (I : Ideal A) :
    (toAwayQuotient f I).comp (algebraMap A (specializing f I)) =
      Localization.toAwayQuotient f I :=
  sorry

/-- The canonical map `specializing f I →+* (A ⧸ I)_f` is surjective. -/
theorem toAwayQuotient_surjective (f : A) (I : Ideal A) :
    Function.Surjective (toAwayQuotient f I) :=
  sorry

/-- The image of `Spec(specializing f I) → Spec(A)` is the set of points
specializing to `D(f) ∩ V(I)`. Combined with
`PrimeSpectrum.localization_comap_isEmbedding`, this map is a homeomorphism
onto that set. -/
theorem comap_range (f : A) (I : Ideal A) :
    Set.range (PrimeSpectrum.comap (algebraMap A (specializing f I))) =
      PrimeSpectrum.specializesTo (PrimeSpectrum.basicLocallyClosed f I) :=
  sorry

/-- If a ring homomorphism sends the specializing multiplicative set into a
target specializing multiplicative set, it induces a map of localizations. -/
theorem le_comap_of_mapsTo {A' : Type u} [CommRing A'] (φ : A →+* A')
    (f : A) (I : Ideal A) (f' : A') (I' : Ideal A')
    (hZ : Set.MapsTo (PrimeSpectrum.comap φ)
      (PrimeSpectrum.basicLocallyClosed f' I')
      (PrimeSpectrum.basicLocallyClosed f I)) :
    specializingSubmonoid f I ≤
      Submonoid.comap φ (specializingSubmonoid f' I') :=
  sorry

/-- A ring map sending `D(f') ∩ V(I')` into `D(f) ∩ V(I)` induces a unique
`A`-algebra map of specializing localizations. -/
theorem existsUnique_map {A' : Type u} [CommRing A'] (φ : A →+* A')
    (f : A) (I : Ideal A) (f' : A') (I' : Ideal A')
    (hZ : Set.MapsTo (PrimeSpectrum.comap φ)
      (PrimeSpectrum.basicLocallyClosed f' I')
      (PrimeSpectrum.basicLocallyClosed f I)) :
    ∃! ψ : specializing f I →+* specializing f' I',
      ψ.comp (algebraMap A (specializing f I)) =
        (algebraMap A' (specializing f' I')).comp φ :=
  sorry

end Specializing

end Localization
