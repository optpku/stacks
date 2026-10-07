module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Étale-local germ transfer at a point of an algebraic space

An étale-local property of scheme germs may be tested on étale morphisms from schemes through a
fixed point of an algebraic space: the “for any chart” and “for some chart” conditions are the
basic predicates.
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

end AlgebraicGeometry.AlgebraicSpace
