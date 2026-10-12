/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.QuotientLift.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.Basic

@[expose] public section

/-!
# Syntomic quotient lifts

This file adds syntomicity to the neutral quotient-lift datum and states its
canonical existence API for quotient maps and arbitrary surjections.
-/

universe u v w x

namespace RingHom.QuotientLift

variable {R : Type u} {R₀ : Type v} [CommRing R] [CommRing R₀]

/-- A quotient lift whose upstairs algebra map is syntomic. -/
@[stacks 07M8 "syntomic quotient lift datum"]
structure Syntomic (q : R →+* R₀) (A₀ : Type w)
    [CommRing A₀] [Algebra R₀ A₀]
    extends toQuotientLift : RingHom.QuotientLift.{u, v, w, x} q A₀ where
  /-- The upstairs algebra map is syntomic. -/
  syntomic : (algebraMap R upstairs).Syntomic

namespace Syntomic

variable {q : R →+* R₀} {A₀ : Type w} [CommRing A₀] [Algebra R₀ A₀]

/-- Attach syntomicity to an existing quotient lift. -/
def of (L : RingHom.QuotientLift q A₀)
    (syntomic : (algebraMap R L.upstairs).Syntomic) :
    Syntomic q A₀ :=
  { toQuotientLift := L
    syntomic := syntomic }

/-- Attaching syntomicity preserves the underlying quotient lift. -/
@[simp]
theorem toQuotientLift_of (L : RingHom.QuotientLift q A₀)
    (syntomic : (algebraMap R L.upstairs).Syntomic) :
    (of L syntomic).toQuotientLift = L := sorry

/-- The syntomic property and comparison equation of a syntomic lift. -/
theorem spec (L : Syntomic q A₀) :
    And ((algebraMap R L.upstairs).Syntomic)
      (L.equiv.toRingHom.comp
          ((Ideal.Quotient.mk ((RingHom.ker q).map (algebraMap R L.upstairs))).comp
            (algebraMap R L.upstairs)) =
        (algebraMap R₀ A₀).comp q) := sorry

end Syntomic

end RingHom.QuotientLift

namespace Algebra.Syntomic

variable {R : Type u} {A₀ : Type v} [CommRing R] {I : Ideal R}
variable [CommRing A₀] [Algebra (R ⧸ I) A₀]

/-- A syntomic algebra over a quotient ring lifts to a syntomic quotient lift
over the original ring. -/
@[stacks 07M8 "syntomic algebras lift along quotients"]
theorem exists_lift_of_quotient
    (hA₀ : (algebraMap (R ⧸ I) A₀).Syntomic) :
    Nonempty (RingHom.QuotientLift.Syntomic.{u, u, v, max u v}
      (Ideal.Quotient.mk I) A₀) := sorry

/-- Proposition 16.3.2 (1): a syntomic algebra lifts along an arbitrary
surjective base map, compatibly with reduction by the kernel. -/
@[stacks 07M8]
theorem exists_lift_of_surjective
    {R₀ : Type v} {A₀ : Type w} [CommRing R₀] [CommRing A₀] [Algebra R₀ A₀]
    (q : R →+* R₀) (hq : Function.Surjective q)
    (hA₀ : (algebraMap R₀ A₀).Syntomic) :
    Nonempty (RingHom.QuotientLift.Syntomic.{u, v, w, max u v w} q A₀) := sorry

end Algebra.Syntomic
