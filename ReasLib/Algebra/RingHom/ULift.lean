/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.ULift

@[expose] public section

/-!
# Universe lifts of ring homomorphisms

This leaf provides the one-sided universe lift needed to place a ring
homomorphism in a common-universe concrete category while leaving its domain
unchanged.
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lift both ends of a ring homomorphism to their common maximum universe.
This is the canonical representative used by APIs whose ambient category
requires ring and module carriers in one universe. -/
abbrev uliftMax (f : R →+* S) :
    ULift.{max u v} R →+* ULift.{max u v} S :=
  f.ulift

/-- Lift only the codomain of a ring homomorphism to a chosen universe. -/
noncomputable def uliftCodomain.{w} (f : R →+* S) : R →+* ULift.{w} S :=
  (ULift.ringEquiv.symm : S ≃+* ULift.{w} S).toRingHom.comp f

/-- Evaluation of the codomain universe lift. -/
@[simp]
theorem uliftCodomain_apply (f : R →+* S) (x : R) :
    f.uliftCodomain x = ⟨f x⟩ := sorry

/-- Lowering the codomain after `uliftCodomain` recovers the original ring
homomorphism. -/
@[simp]
theorem down_comp_uliftCodomain (f : R →+* S) :
    ULift.ringEquiv.toRingHom.comp f.uliftCodomain = f := sorry

end RingHom
