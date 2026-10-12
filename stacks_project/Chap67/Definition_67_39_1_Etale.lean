/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Pointwise étaleness of morphisms of algebraic spaces

A morphism of algebraic spaces is étale at a point when it is étale after
restriction to an open subspace neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is étale at a point `x` of `X`
if it is étale after restriction to some open subspace neighbourhood of `x`. -/
def EtaleAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Etale (i ≫ f)

/-- Étaleness at a point is the existence of an open subspace neighbourhood on
which the morphism is étale. -/
theorem etaleAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    EtaleAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Etale (i ≫ f) :=
  sorry

namespace EtaleAt

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` is étale witnesses
that `f` is étale at every point of the image of `|X'|`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [Etale (i ≫ f)] : EtaleAt f x :=
  sorry

end EtaleAt

/-- An étale morphism of algebraic spaces is étale at every point of its source. -/
theorem etaleAt_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] (x : Points X) : EtaleAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
