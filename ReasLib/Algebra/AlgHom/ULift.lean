/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import ReasLib.Algebra.RingHom.ULift

@[expose] public section

/-!
# Universe lifts of algebra homomorphisms

This file provides both a one-sided codomain lift and a common-universe lift.
The latter includes the base-ring universe so that intermediate algebras do
not suffer a hidden universe restriction.
-/

universe u v w

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Lift only the codomain of an algebra homomorphism to a chosen universe. -/
noncomputable def uliftCodomain.{x} (f : A →ₐ[R] B) : A →ₐ[R] ULift.{x} B :=
  ULift.algEquiv.symm.toAlgHom.comp f

/-- The underlying ring map of an algebra-homomorphism codomain lift is the
corresponding ring-homomorphism lift. -/
theorem uliftCodomain_toRingHom (f : A →ₐ[R] B) :
    f.uliftCodomain.toRingHom = f.toRingHom.uliftCodomain := sorry

/-- Lowering the codomain after `uliftCodomain` recovers the original algebra
homomorphism. -/
theorem down_comp_uliftCodomain (f : A →ₐ[R] B) :
    ULift.algEquiv.toAlgHom.comp f.uliftCodomain = f := sorry

/-- Lift the source and target of an algebra homomorphism to the common
universe containing the base, source, and target. -/
noncomputable def uliftMap (f : A →ₐ[R] B) :
    ULift.{max u w} A →ₐ[R] ULift.{max u v} B :=
  f.uliftCodomain.comp ULift.algEquiv.toAlgHom

/-- Lowering both sides of `uliftMap` recovers the original algebra
homomorphism. -/
theorem down_comp_uliftMap_comp_up (f : A →ₐ[R] B) :
    ULift.algEquiv.toAlgHom.comp
        (f.uliftMap.comp ULift.algEquiv.symm.toAlgHom) = f := sorry

end AlgHom
