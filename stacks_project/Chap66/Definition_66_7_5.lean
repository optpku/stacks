/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_7_4

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Definition 66.7.5: let `S` be a scheme, let `X` be an algebraic space over `S`,
let `x` be a point of `|X|`, and let `P` be a property of germs of schemes which is
étale local. We say `X` has property `P` at `x` if any of the equivalent conditions
of Lemma 66.7.4 hold. -/
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

namespace hasEtaleLocalAt

/-- An étale morphism from a scheme through `x` on which `P` holds witnesses
`hasEtaleLocalAt P hP X x`. -/
theorem of {S : Scheme.{u}} {P : GermProperty.{u}} (hP : P.IsEtaleLocal)
    {X : AlgebraicSpace S} {x : Points X} {U : Over S} (a : ofOver U ⟶ X) (u : U.left)
    (h_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hx : Points.mapOfOver a u = x) (hPu : P U.left u) : hasEtaleLocalAt P hP X x :=
  existsEtaleAt.of a u h_etale hx hPu

/-- An algebraic space satisfying `hasEtaleLocalAt P hP X x` admits an étale scheme
chart through `x` on which `P` holds. -/
theorem spec {S : Scheme.{u}} {P : GermProperty.{u}} (hP : P.IsEtaleLocal)
    {X : AlgebraicSpace S} {x : Points X} (h : hasEtaleLocalAt P hP X x) :
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
        Points.mapOfOver a u = x ∧ P U.left u :=
  h

end hasEtaleLocalAt

/-- If `P` is étale-local, then `X` has property `P` at `x` if and only if every étale
morphism from a scheme through `x` has property `P` at the source point. -/
theorem hasEtaleLocalAt_iff_forallEtaleAt {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (X : AlgebraicSpace S) (x : Points X) :
    hasEtaleLocalAt P hP X x ↔ forallEtaleAt P X x :=
  sorry

/-- If `T` is a scheme over `S`, then `ofOver T` has an étale-local germ property `P`
at the image of `x` if and only if `P` holds at `(T.left, x)`. -/
theorem hasEtaleLocalAt_ofOver {S : Scheme.{u}} (P : GermProperty.{u})
    (hP : P.IsEtaleLocal) (T : Over S) (x : T.left) :
    hasEtaleLocalAt P hP (ofOver T) (ofOver.pointsEquiv T x) ↔ P T.left x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
