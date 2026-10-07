module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import ReasLib.RingTheory.RingHom.QuotientLift.Smooth

@[expose] public section

/-!
# Standard-smooth quotient lifts

This file owns standard-smooth quotient lifts, their forgetful maps, and the
surjection-level lifting API used by standard-open covers.
-/

universe u v w x

namespace RingHom.QuotientLift

variable {R : Type u} {R₀ : Type v} [CommRing R] [CommRing R₀]

/-- A quotient lift whose upstairs algebra is standard smooth. -/
@[stacks 04B1 "standard-smooth quotient lift datum"]
structure StandardSmooth (q : R →+* R₀) (A₀ : Type w)
    [CommRing A₀] [Algebra R₀ A₀]
    extends toQuotientLift : RingHom.QuotientLift.{u, v, w, x} q A₀ where
  /-- Standard smoothness of the upstairs algebra. -/
  [standardSmooth : Algebra.IsStandardSmooth R upstairs]

attribute [instance] StandardSmooth.standardSmooth

namespace StandardSmooth

variable {q : R →+* R₀} {A₀ : Type w} [CommRing A₀] [Algebra R₀ A₀]

/-- Attach standard smoothness to an existing quotient lift. -/
def of (L : RingHom.QuotientLift q A₀)
    [Algebra.IsStandardSmooth R L.upstairs] : StandardSmooth q A₀ :=
  { toQuotientLift := L
    standardSmooth := inferInstanceAs (Algebra.IsStandardSmooth R L.upstairs) }

/-- Attaching standard smoothness preserves the underlying quotient lift. -/
@[simp]
theorem toQuotientLift_of (L : RingHom.QuotientLift q A₀)
    [Algebra.IsStandardSmooth R L.upstairs] :
    (of L).toQuotientLift = L := sorry

/-- Forget standard smoothness while retaining the induced smoothness and the
same quotient-lift data. -/
def toSmooth (L : StandardSmooth q A₀) : Smooth q A₀ :=
  { toQuotientLift := L.toQuotientLift
    smooth := inferInstanceAs (Algebra.Smooth R L.upstairs) }

/-- Forgetting standard smoothness preserves the underlying quotient lift. -/
@[simp]
theorem toSmooth_toQuotientLift (L : StandardSmooth q A₀) :
    L.toSmooth.toQuotientLift = L.toQuotientLift := sorry

/-- Forget standard smoothness while retaining the induced syntomicity. -/
def toSyntomic (L : StandardSmooth q A₀) : Syntomic q A₀ :=
  L.toSmooth.toSyntomic

/-- Forgetting standard smoothness down to syntomicity preserves the
underlying quotient lift. -/
@[simp]
theorem toSyntomic_toQuotientLift (L : StandardSmooth q A₀) :
    L.toSyntomic.toQuotientLift = L.toQuotientLift := sorry

/-- The standard-smooth property and comparison equation of a lift. -/
theorem spec (L : StandardSmooth q A₀) :
    And (Algebra.IsStandardSmooth R L.upstairs)
      (L.equiv.toRingHom.comp
          ((Ideal.Quotient.mk ((RingHom.ker q).map (algebraMap R L.upstairs))).comp
            (algebraMap R L.upstairs)) =
        (algebraMap R₀ A₀).comp q) := sorry

end StandardSmooth

end RingHom.QuotientLift

namespace Algebra.IsStandardSmooth

variable {R : Type u} {T : Type v} [CommRing R] {I : Ideal R}
variable [CommRing T] [Algebra (R ⧸ I) T]

/-- A standard-smooth algebra over `R ⧸ I` lifts to a compatible
standard-smooth quotient lift over `R`. -/
@[stacks 04B1 "standard-smooth quotient lift"]
theorem exists_lift_of_quotient [hT : IsStandardSmooth (R ⧸ I) T] :
    Nonempty (RingHom.QuotientLift.StandardSmooth.{u, u, v, max u v}
      (Ideal.Quotient.mk I) T) := sorry

/-- A standard-smooth algebra lifts along an arbitrary surjective base map. -/
@[stacks 04B1 "standard-smooth lift along a surjection"]
theorem exists_lift_of_surjective
    {R₀ : Type v} {A₀ : Type w}
    [CommRing R₀] [CommRing A₀] [Algebra R₀ A₀]
    (q : R →+* R₀) (hq : Function.Surjective q)
    [IsStandardSmooth R₀ A₀] :
    Nonempty
      (RingHom.QuotientLift.StandardSmooth.{u, v, w, max u v w} q A₀) := sorry

end Algebra.IsStandardSmooth
