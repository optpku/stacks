/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# Quotient lifts of algebras

This file owns the property-neutral comparison datum for lifting an algebra
across a ring map. Geometric properties of the upstairs algebra live in
separate leaves.
-/

universe u v w x

namespace RingHom

variable {R : Type u} {R₀ : Type v} [CommRing R] [CommRing R₀]

/-- A lift of an `R₀`-algebra across `q : R →+* R₀`, with its kernel
quotient and compatibility equation made explicit. -/
@[stacks 07M8 "quotient lift datum"]
structure QuotientLift (q : R →+* R₀) (A₀ : Type w)
    [CommRing A₀] [Algebra R₀ A₀] where
  /-- The lifted algebra over `R`. -/
  upstairs : Type x
  /-- The commutative-ring structure on the lifted algebra. -/
  instCommRing : CommRing upstairs
  /-- The `R`-algebra structure on the lifted algebra. -/
  instAlgebra : Algebra R upstairs
  /-- The comparison isomorphism after reduction. -/
  equiv :
    (upstairs ⧸ (RingHom.ker q).map (algebraMap R upstairs)) ≃+* A₀
  /-- The comparison is compatible with the two structure maps. -/
  commutes :
    equiv.toRingHom.comp
        ((Ideal.Quotient.mk ((RingHom.ker q).map (algebraMap R upstairs))).comp
          (algebraMap R upstairs)) =
      (algebraMap R₀ A₀).comp q

attribute [instance] QuotientLift.instCommRing QuotientLift.instAlgebra

namespace QuotientLift

variable {q : R →+* R₀} {A₀ : Type w} [CommRing A₀] [Algebra R₀ A₀]

/-- The kernel quotient of the lifted algebra. -/
abbrev reduction (L : QuotientLift q A₀) :=
  L.upstairs ⧸ (RingHom.ker q).map (algebraMap R L.upstairs)

/-- Build a quotient lift from its upstairs algebra, comparison equivalence,
and compatibility equation. -/
def ofEquiv {A : Type x} [CommRing A] [Algebra R A]
    (e : (A ⧸ (RingHom.ker q).map (algebraMap R A)) ≃+* A₀)
    (commutes :
      e.toRingHom.comp
          ((Ideal.Quotient.mk ((RingHom.ker q).map (algebraMap R A))).comp
            (algebraMap R A)) =
        (algebraMap R₀ A₀).comp q) :
    QuotientLift q A₀ :=
  { upstairs := A
    instCommRing := inferInstance
    instAlgebra := inferInstance
    equiv := e
    commutes := commutes }

/-- The upstairs algebra of `ofEquiv` is the supplied algebra. -/
@[simp]
theorem upstairs_ofEquiv {A : Type x} [CommRing A] [Algebra R A]
    (e : (A ⧸ (RingHom.ker q).map (algebraMap R A)) ≃+* A₀)
    (commutes :
      e.toRingHom.comp
          ((Ideal.Quotient.mk ((RingHom.ker q).map (algebraMap R A))).comp
            (algebraMap R A)) =
        (algebraMap R₀ A₀).comp q) :
    (ofEquiv e commutes).upstairs = A := sorry

/-- The reduction equivalence of `ofEquiv` is the supplied equivalence. -/
@[simp]
theorem equiv_ofEquiv {A : Type x} [CommRing A] [Algebra R A]
    (e : (A ⧸ (RingHom.ker q).map (algebraMap R A)) ≃+* A₀)
    (commutes :
      e.toRingHom.comp
          ((Ideal.Quotient.mk ((RingHom.ker q).map (algebraMap R A))).comp
            (algebraMap R A)) =
        (algebraMap R₀ A₀).comp q) :
    (ofEquiv e commutes).equiv = e := sorry

/-- The compatibility specification carried by a quotient lift. -/
theorem spec (L : QuotientLift q A₀) :
    L.equiv.toRingHom.comp
        ((Ideal.Quotient.mk ((RingHom.ker q).map (algebraMap R L.upstairs))).comp
          (algebraMap R L.upstairs)) =
      (algebraMap R₀ A₀).comp q := sorry

end QuotientLift

end RingHom
