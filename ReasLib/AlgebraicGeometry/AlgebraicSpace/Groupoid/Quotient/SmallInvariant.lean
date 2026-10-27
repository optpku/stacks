/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Invariant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation

/-!
# Invariant morphisms out of a groupoid in algebraic spaces

A morphism from the object space of a groupoid in algebraic spaces to an
algebraic space is `R`-invariant when it equalizes source and target. The
atlas composite recovers such a morphism from a map out of the quotient stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A morphism `φ : U ⟶ Y` of algebraic spaces over `S` is `R`-invariant for a
groupoid `G` in algebraic spaces when it equalizes the source and target maps
of `G`. -/
def IsInvariantHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) : Prop :=
  G.t.left ≫ φ = G.s.left ≫ φ

/-- `R`-invariance of a morphism of algebraic spaces over `S` is equalization of
the source and target maps. -/
theorem isInvariantHom_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) :
    G.IsInvariantHom φ ↔ G.t.left ≫ φ = G.s.left ≫ φ := sorry

/-- Left-level `R`-invariance of a morphism over `B` agrees with invariance for
the underlying pre-relation. -/
theorem isInvariantHom_iff_toPreRelation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : Over B} (ψ : G.U ⟶ X) :
    G.IsInvariantHom ψ.left ↔ G.toPreRelation.IsInvariantHom ψ := sorry

/-- The composite `U ⟶ [U / R] ⟶ Y` recovered from a morphism of the quotient
stack to an algebraic space. -/
def atlasComp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids) : G.U.left ⟶ Y :=
  AlgebraicSpace.toGroupoids.eval (SmallQuotient.atlas G ≫ f)

/-- `atlasComp f` is evaluation of the composite of the atlas with `f`. -/
theorem atlasComp_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (f : (SmallQuotient.quotientStack G) ⟶ Y.toGroupoids) :
    G.atlasComp f = AlgebraicSpace.toGroupoids.eval (SmallQuotient.atlas G ≫ f) := sorry

/-- A morphism from the quotient stack of a flat, locally finitely presented
groupoid to an algebraic space restricts to an invariant morphism, characterized
uniquely by factorization of its atlas composite through the represented map. -/
theorem isInvariantHom_atlasComp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : SmallQuotient.quotientStack G ⟶ Y.toGroupoids) :
    G.IsInvariantHom (G.atlasComp f) ∧
      ∀ φ : G.U.left ⟶ Y,
        (Nonempty (SmallQuotient.atlas G ≫ f ≅ AlgebraicSpace.toGroupoids.map φ) ↔
          φ = G.atlasComp f) := sorry

/-- Every invariant morphism from the object space of a flat, locally finitely
presented groupoid to an algebraic space descends to its quotient stack,
uniquely up to 2-isomorphism among morphisms with the given atlas composite. -/
theorem existsUnique_hom_of_isInvariantHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ) :
    ∃ f : SmallQuotient.quotientStack G ⟶ Y.toGroupoids,
      Nonempty (SmallQuotient.atlas G ≫ f ≅ AlgebraicSpace.toGroupoids.map φ) ∧
        (∀ g : SmallQuotient.quotientStack G ⟶ Y.toGroupoids,
          Nonempty (SmallQuotient.atlas G ≫ g ≅ AlgebraicSpace.toGroupoids.map φ) →
            Nonempty (f ≅ g)) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
