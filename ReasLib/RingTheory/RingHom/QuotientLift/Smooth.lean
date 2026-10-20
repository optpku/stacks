module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.RingTheory.RingHom.QuotientLift.Syntomic

@[expose] public section

/-!
# Smooth quotient lifts

This file adds smoothness to quotient lifts and exposes the canonical
forgetful map to syntomic quotient lifts.
-/

universe u v w x

namespace RingHom.QuotientLift

variable {R : Type u} {R₀ : Type v} [CommRing R] [CommRing R₀]

/-- A quotient lift whose upstairs algebra is smooth. -/
@[stacks 07M8 "smooth quotient lift datum"]
structure Smooth (q : R →+* R₀) (A₀ : Type w)
    [CommRing A₀] [Algebra R₀ A₀]
    extends toQuotientLift : RingHom.QuotientLift.{u, v, w, x} q A₀ where
  /-- Smoothness of the upstairs algebra. -/
  [smooth : Algebra.Smooth R upstairs]

attribute [instance] Smooth.smooth

namespace Smooth

variable {q : R →+* R₀} {A₀ : Type w} [CommRing A₀] [Algebra R₀ A₀]

/-- Attach smoothness to an existing quotient lift. -/
def of (L : RingHom.QuotientLift q A₀)
    [Algebra.Smooth R L.upstairs] : Smooth q A₀ :=
  { toQuotientLift := L
    smooth := inferInstanceAs (Algebra.Smooth R L.upstairs) }

/-- Attaching smoothness preserves the underlying quotient lift. -/
@[simp]
theorem toQuotientLift_of (L : RingHom.QuotientLift q A₀)
    [Algebra.Smooth R L.upstairs] :
    (of L).toQuotientLift = L := sorry

/-- The upstairs algebra map of a smooth quotient lift is syntomic. -/
theorem syntomic (L : Smooth q A₀) :
    (algebraMap R L.upstairs).Syntomic := sorry

/-- Forget smoothness while retaining syntomicity and the same quotient-lift
data. -/
def toSyntomic (L : Smooth q A₀) : Syntomic q A₀ :=
  Syntomic.of L.toQuotientLift L.syntomic

/-- Forgetting smoothness preserves the underlying quotient lift. -/
@[simp]
theorem toSyntomic_toQuotientLift (L : Smooth q A₀) :
    L.toSyntomic.toQuotientLift = L.toQuotientLift := sorry

/-- The smoothness and comparison equation of a smooth lift. -/
theorem spec (L : Smooth q A₀) :
    And (Algebra.Smooth R L.upstairs)
      (L.equiv.toRingHom.comp
          ((Ideal.Quotient.mk ((RingHom.ker q).map (algebraMap R L.upstairs))).comp
            (algebraMap R L.upstairs)) =
        (algebraMap R₀ A₀).comp q) := sorry

end Smooth

end RingHom.QuotientLift

namespace Algebra.Smooth

variable {R : Type u} {Sbar : Type v} [CommRing R] {I : Ideal R}
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar]

/-- A smooth algebra over a quotient ring lifts to a smooth quotient lift over
the original ring. -/
@[stacks 07M8 "smooth algebras lift along quotients"]
theorem exists_lift_of_quotient [Smooth (R ⧸ I) Sbar] :
    Nonempty (RingHom.QuotientLift.Smooth.{u, u, v, max u v}
      (Ideal.Quotient.mk I) Sbar) := sorry

/-- Proposition 16.3.2 (2): smooth algebras lift along an arbitrary
surjective base map, compatibly with reduction by the kernel. -/
@[stacks 07M8]
theorem exists_lift_of_surjective
    {R₀ : Type v} {A₀ : Type w} [CommRing R₀] [CommRing A₀] [Algebra R₀ A₀]
    (q : R →+* R₀) (hq : Function.Surjective q) [Smooth R₀ A₀] :
    Nonempty (RingHom.QuotientLift.Smooth.{u, v, w, max u v w} q A₀) := sorry

end Algebra.Smooth
