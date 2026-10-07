module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty
public import stacks_project.Chap66.Lemma_66_7_4

/-!
# Local-ring properties as étale-local germ properties

A property of local rings that is invariant under étale maps at corresponding primes
determines an étale-local property of scheme germs via stalks. On an algebraic space,
“the local ring at `x` has `P`” is the existence of an étale scheme chart through `x`
on which this germ property holds.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

/-- A property of local rings is étale-local at corresponding primes when it is invariant
under étale ring maps: for `Algebra.Etale A B` and `q : PrimeSpectrum B`, `P` holds at
`Localization.AtPrime (q.asIdeal.under A)` if and only if it holds at
`Localization.AtPrime q.asIdeal`. -/
def IsEtaleLocalAtPrimes
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop) : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : PrimeSpectrum B),
    P (Localization.AtPrime (q.asIdeal.under A)) ↔
      P (Localization.AtPrime q.asIdeal)

/-- Explicit unfolding of étale-invariance of a local-ring property at corresponding primes. -/
theorem isEtaleLocalAtPrimes_iff
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop) :
    IsEtaleLocalAtPrimes P ↔
      ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
        (q : PrimeSpectrum B),
        P (Localization.AtPrime (q.asIdeal.under A)) ↔
          P (Localization.AtPrime q.asIdeal) :=
  Iff.rfl

namespace IsEtaleLocalAtPrimes

/-- Transport a local-ring property along the prime localizations of an étale algebra. -/
theorem iff_of {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop}
    (hP : IsEtaleLocalAtPrimes P) {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] (q : PrimeSpectrum B) :
    P (Localization.AtPrime (q.asIdeal.under A)) ↔
      P (Localization.AtPrime q.asIdeal) :=
  hP q

end IsEtaleLocalAtPrimes

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

/-- If `P` is étale-local at corresponding primes, then `ofLocalRing P` is an étale-local
property of scheme germs. -/
theorem isEtaleLocal {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop}
    (hP : IsEtaleLocalAtPrimes P) : (ofLocalRing P).IsEtaleLocal :=
  sorry

end ofLocalRing

end GermProperty

namespace AlgebraicSpace

/-- The local ring of an algebraic space `X` at a point `x` has property `P` when some étale
scheme chart through `x` has stalk satisfying `P`. -/
def localRingHas {S : Scheme.{u}}
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (X : AlgebraicSpace S) (x : Points X) : Prop :=
  existsEtaleAt (GermProperty.ofLocalRing P) X x

/-- `localRingHas P X x` is the existence of an étale scheme chart through `x` on which
`ofLocalRing P` holds. -/
theorem localRingHas_def {S : Scheme.{u}}
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (X : AlgebraicSpace S) (x : Points X) :
    localRingHas P X x ↔ existsEtaleAt (GermProperty.ofLocalRing P) X x :=
  Iff.rfl

/-- `localRingHas P X x` is equivalent to the existence of an étale scheme chart through `x`
on which `ofLocalRing P` holds. -/
theorem localRingHas_iff_existsEtaleAt {S : Scheme.{u}}
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (X : AlgebraicSpace S) (x : Points X) :
    localRingHas P X x ↔ existsEtaleAt (GermProperty.ofLocalRing P) X x :=
  Iff.rfl

namespace localRingHas

/-- An étale scheme chart through `x` whose stalk has property `P` witnesses
`localRingHas P X x`. -/
theorem of {S : Scheme.{u}} {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop}
    {X : AlgebraicSpace S} {x : Points X} {U : Over S} (a : ofOver U ⟶ X) (u : U.left)
    (h_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hx : Points.mapOfOver a u = x) (hP : P (U.left.presheaf.stalk u)) :
    localRingHas P X x :=
  existsEtaleAt.of a u h_etale hx hP

/-- An algebraic space satisfying `localRingHas P X x` admits an étale scheme chart through
`x` whose stalk has property `P`. -/
theorem spec {S : Scheme.{u}} {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop}
    {X : AlgebraicSpace S} {x : Points X} (h : localRingHas P X x) :
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
        Points.mapOfOver a u = x ∧ P (U.left.presheaf.stalk u) :=
  h

end localRingHas

/-- If `ofLocalRing P` is étale-local, then the local ring of `X` at `x` has `P` if and only
if every étale scheme chart through `x` has stalk satisfying `P`. -/
theorem localRingHas_iff_forallEtaleAt {S : Scheme.{u}}
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (hP : (GermProperty.ofLocalRing P).IsEtaleLocal)
    (X : AlgebraicSpace S) (x : Points X) :
    localRingHas P X x ↔ forallEtaleAt (GermProperty.ofLocalRing P) X x :=
  sorry

/-- If `ofLocalRing P` is étale-local and `T` is a scheme over `S`, then the local ring of
`ofOver T` at the image of `t` has `P` if and only if the stalk of `T` at `t` has `P`. -/
theorem localRingHas_ofOver {S : Scheme.{u}}
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (hP : (GermProperty.ofLocalRing P).IsEtaleLocal) (T : Over S) (t : T.left) :
    localRingHas P (ofOver T) (ofOver.pointsEquiv T t) ↔
      P (T.left.presheaf.stalk t) :=
  sorry

end AlgebraicSpace

end AlgebraicGeometry
