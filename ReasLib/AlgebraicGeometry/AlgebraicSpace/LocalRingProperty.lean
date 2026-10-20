/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GermProperty

/-!
# Local-ring properties on algebraic spaces

A local-ring property holds at a point of an algebraic space when it holds on the stalk
of an étale scheme chart through that point. For étale-local germ properties this agrees
with the universal chart condition and with stalk evaluation on schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- The local ring of an algebraic space `X` at a point `x` has property `P` when some étale
scheme chart through `x` has stalk satisfying `P`. -/
def localRingHas {S : Scheme.{u}}
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (X : AlgebraicSpace S) (x : Points X) : Prop :=
  existsEtaleAt (GermProperty.ofLocalRing P) X x

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
  (forallEtaleAt_iff_existsEtaleAt (GermProperty.ofLocalRing P) hP X x).symm

/-- If `ofLocalRing P` is étale-local and `T` is a scheme over `S`, then the local ring of
`ofOver T` at the image of `t` has `P` if and only if the stalk of `T` at `t` has `P`. -/
theorem localRingHas_ofOver {S : Scheme.{u}}
    (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (hP : (GermProperty.ofLocalRing P).IsEtaleLocal) (T : Over S) (t : T.left) :
    localRingHas P (ofOver T) (ofOver.pointsEquiv T t) ↔
      P (T.left.presheaf.stalk t) :=
  existsEtaleAt_ofOver (GermProperty.ofLocalRing P) hP T t

end AlgebraicSpace

end AlgebraicGeometry
