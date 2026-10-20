module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Quotient.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
  AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The largest exceptional-ideal containment exponent of an ideal containing a power of the
maximal ideal and contained in the maximal ideal is positive on the maximal-ideal blowup of a
two-dimensional regular local ring. -/
theorem maximalExceptionalPowerExponent_pos
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) (I : Ideal A)
    (h_power : (IsLocalRing.maximalIdeal A) ^ n ≤ I)
    (h_maximal : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (h_contained : (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d)
    (h_largest : ∀ e : ℕ,
      (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
        exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ e → e ≤ d) :
    0 < d := sorry

/-- Removing the largest exceptional-ideal power from an ideal containing a power of the
maximal ideal on a two-dimensional regular-local blowup yields a quotient supported at finitely
many closed points. -/
theorem residualIdealQuotient_hasFiniteClosedSupport
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) (I : Ideal A)
    (h_power : (IsLocalRing.maximalIdeal A) ^ n ≤ I)
    (h_maximal : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (h_contained : (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d)
    (h_largest : ∀ e : ℕ,
      (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
        exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ e → e ≤ d)
    (I' : X.IdealSheafData)
    (h_residual : (Scheme.idealSheafDataOfIdealOnSpec I).comap f =
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d * I') :
    ∃ (r : ℕ) (x : Fin r ↪ X),
      (∀ i, x i ∈ closedPoints X) ∧
        RingedSpace.moduleSupport (cokernel I'.toSubobject.arrow) = Set.range x := sorry

/-- On the maximal-ideal blowup of a two-dimensional regular local ring, the quotient by an
ideal containing a power of the maximal ideal and contained in the maximal ideal has length
strictly greater than the global sections of the residual-ideal quotient. -/
theorem length_quotient_gt_residualIdealCohomology
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) (I : Ideal A)
    (h_power : (IsLocalRing.maximalIdeal A) ^ n ≤ I)
    (h_maximal : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (h_contained : (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d)
    (h_largest : ∀ e : ℕ,
      (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
        exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ e → e ≤ d)
    (I' : X.IdealSheafData)
    (h_residual : (Scheme.idealSheafDataOfIdealOnSpec I).comap f =
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d * I') :
    Module.length A (A ⧸ I) >
      Module.length A (Scheme.Hom.cohomology f (cokernel I'.toSubobject.arrow) 0) := sorry

/-- For a residual ideal on the maximal-ideal blowup of a two-dimensional regular local ring,
the global-sections length over the base ring bounds below the sum of the lengths over the
local stalk rings at its finitely many closed support points. -/
theorem sum_stalkLengths_le_residualIdealCohomologyLength
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))]
    (n : ℕ) (I : Ideal A)
    (h_power : (IsLocalRing.maximalIdeal A) ^ n ≤ I)
    (h_maximal : I ≤ IsLocalRing.maximalIdeal A) (d : ℕ)
    (h_contained : (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d)
    (h_largest : ∀ e : ℕ,
      (Scheme.idealSheafDataOfIdealOnSpec I).comap f ≤
        exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ e → e ≤ d)
    (I' : X.IdealSheafData)
    (h_residual : (Scheme.idealSheafDataOfIdealOnSpec I).comap f =
      exceptionalIdeal (IsLocalRing.maximalIdeal A) f ^ d * I')
    (r : ℕ) (x : Fin r ↪ X) (h_closed : ∀ i, x i ∈ closedPoints X)
    (h_support : RingedSpace.moduleSupport (cokernel I'.toSubobject.arrow) = Set.range x) :
    Module.length A (Scheme.Hom.cohomology f (cokernel I'.toSubobject.arrow) 0) ≥
      ∑ i, Module.length (X.presheaf.stalk (x i))
        (stalkQuotient I'.toSubobject (x i)) := sorry

end AlgebraicGeometry.IsBlowup
