/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.LocalProperty
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty

/-!
# Stalkwise local-ring properties

A property of commutative local rings gives a property of scheme germs by evaluation on
stalks. Isomorphism invariance and invariance at étale prime localizations make it étale local.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace GermProperty

/-- The germ property attached to a property of local rings by evaluating `P` on the stalk
`X.presheaf.stalk x`. -/
def ofLocalRing (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop) :
    GermProperty.{u} :=
  fun X x ↦ P (X.presheaf.stalk x)

/-- `ofLocalRing P` is the stalkwise evaluation of `P`. -/
theorem ofLocalRing_apply (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (X : Scheme.{u}) (x : X) :
    ofLocalRing P X x = P (X.presheaf.stalk x) :=
  rfl

/-- A scheme germ satisfies `ofLocalRing P` if and only if the stalk has property `P`. -/
theorem ofLocalRing_iff (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (X : Scheme.{u}) (x : X) :
    ofLocalRing P X x ↔ P (X.presheaf.stalk x) :=
  Iff.rfl

namespace ofLocalRing

/-- An isomorphism-invariant property of local rings that is étale-local at corresponding
primes induces an étale-local property of scheme germs by stalk evaluation. -/
theorem isEtaleLocal {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop}
    (hIso : LocalRingProperty.RespectsIso P)
    (hP : LocalRingProperty.IsEtaleLocalAtPrimes P) : (ofLocalRing P).IsEtaleLocal :=
  sorry

end ofLocalRing

end GermProperty

end AlgebraicGeometry
