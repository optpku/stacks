/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty

/-!
# Étale-local properties of algebraic-space germs

Properties of scheme germs can be tested on étale scheme charts through a point of an
algebraic space. For an étale-local property, the existential and universal chart conditions
agree and recover the original property on representable algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- There exists a scheme `U` over `S` and an étale morphism `a : ofOver U ⟶ X` together with a
point `u : U.left` such that `Points.mapOfOver a u = x` and `P` holds at `(U.left, u)`. -/
def existsEtaleAt {S : Scheme.{u}} (P : GermProperty.{u}) (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
      Points.mapOfOver a u = x ∧ P U.left u

/-- `existsEtaleAt P X x` is the existence of an étale scheme chart through `x` on which `P`
holds. -/
theorem existsEtaleAt_def {S : Scheme.{u}} (P : GermProperty.{u}) (X : AlgebraicSpace S)
    (x : Points X) :
    existsEtaleAt P X x ↔
      ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
          Points.mapOfOver a u = x ∧ P U.left u :=
  Iff.rfl

namespace existsEtaleAt

/-- An étale morphism from a scheme through `x` on which `P` holds witnesses
`existsEtaleAt P X x`. -/
theorem of {S : Scheme.{u}} {P : GermProperty.{u}} {X : AlgebraicSpace S} {x : Points X}
    {U : Over S} (a : ofOver U ⟶ X) (u : U.left)
    (h_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hx : Points.mapOfOver a u = x) (hP : P U.left u) : existsEtaleAt P X x :=
  ⟨U, a, u, h_etale, hx, hP⟩

/-- An algebraic space satisfying `existsEtaleAt P X x` admits an étale scheme chart through `x`
on which `P` holds. -/
theorem spec {S : Scheme.{u}} {P : GermProperty.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsEtaleAt P X x) :
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
        Points.mapOfOver a u = x ∧ P U.left u :=
  h

end existsEtaleAt

/-- An algebraic space has an étale-local germ property at a point if the property holds at a
point above it in some étale scheme chart. -/
@[stacks 04RC]
def hasEtaleLocalAt {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    (X : AlgebraicSpace S) (x : Points X) : Prop :=
  existsEtaleAt P X x

/-- `hasEtaleLocalAt P hP X x` is the existence of an étale scheme chart through `x`
on which `P` holds. -/
theorem hasEtaleLocalAt_def {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (X : AlgebraicSpace S) (x : Points X) :
    hasEtaleLocalAt P hP X x ↔ existsEtaleAt P X x :=
  Iff.rfl

/-- Every étale morphism `a : ofOver U ⟶ X` from a scheme over `S` and every point `u : U.left`
with `Points.mapOfOver a u = x` has `P` at `(U.left, u)`. -/
def forallEtaleAt {S : Scheme.{u}} (P : GermProperty.{u}) (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
      Points.mapOfOver a u = x → P U.left u

/-- `forallEtaleAt P X x` is the statement that every étale scheme chart through `x` has
property `P` at the source point. -/
theorem forallEtaleAt_def {S : Scheme.{u}} (P : GermProperty.{u}) (X : AlgebraicSpace S)
    (x : Points X) :
    forallEtaleAt P X x ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          Points.mapOfOver a u = x → P U.left u :=
  Iff.rfl

namespace forallEtaleAt

/-- The universal étale-scheme-through-`x` condition witnesses `forallEtaleAt P X x`. -/
theorem of {S : Scheme.{u}} {P : GermProperty.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
        Points.mapOfOver a u = x → P U.left u) :
    forallEtaleAt P X x :=
  h

/-- If `forallEtaleAt P X x`, then every étale morphism from a scheme through `x` has `P` at the
source point. -/
theorem apply {S : Scheme.{u}} {P : GermProperty.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : forallEtaleAt P X x) {U : Over S} (a : ofOver U ⟶ X) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hx : Points.mapOfOver a u = x) : P U.left u :=
  h U a u ha hx

end forallEtaleAt


/-- An étale-local property of scheme germs holds at every étale scheme chart through a point
of an algebraic space if and only if it holds at some such chart. -/
@[stacks 04N2]
theorem forallEtaleAt_iff_existsEtaleAt {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (X : AlgebraicSpace S) (x : Points X) :
    forallEtaleAt P X x ↔ existsEtaleAt P X x :=
  sorry

/-- An étale-local property holds on some étale scheme chart through a point of a representable
algebraic space if and only if it holds at the corresponding scheme point. -/
@[stacks 04N2]
theorem existsEtaleAt_ofOver {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (T : Over S) (x : T.left) :
    existsEtaleAt P (ofOver T) (ofOver.pointsEquiv T x) ↔ P T.left x :=
  sorry

/-- If `T` is a scheme over `S`, then every étale scheme chart of `ofOver T` through the image of
`x` has property `P` if and only if `P` holds at `(T.left, x)`. -/
theorem forallEtaleAt_ofOver {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (T : Over S) (x : T.left) :
    forallEtaleAt P (ofOver T) (ofOver.pointsEquiv T x) ↔ P T.left x :=
  sorry

/-- The étale-local germ criterion at a point transports along an isomorphism to a representable
algebraic space. -/
theorem existsEtaleAt_iso {S : Scheme.{u}} (P : GermProperty.{u}) (hP : P.IsEtaleLocal)
    {X : AlgebraicSpace S} {T : Over S} (e : X ≅ ofOver T) (x : Points X) :
    existsEtaleAt P X x ↔
      P T.left ((ofOver.pointsEquiv T).symm (Points.map e.hom x)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
