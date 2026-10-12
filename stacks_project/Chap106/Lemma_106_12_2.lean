/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Lemma_106_12_2_Invariant
public import stacks_project.Chap97.Theorem_97_17_2

/-!
# Morphisms out of a quotient stack

Morphisms from the quotient stack `[U / R]` of a flat, locally finitely
presented groupoid in algebraic spaces to an algebraic space correspond
one-to-one with `R`-invariant morphisms out of `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 106.12.2 (1). Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, and let `Y` be an algebraic
space. A morphism `f : G.quotientStack ⟶ Y.toGroupoids` yields the
`R`-invariant morphism `G.atlasComp f : G.U.left ⟶ Y`, uniquely recovered as
the factorization of `G.atlas ≫ f` through `AlgebraicSpace.toGroupoids.map`. -/
@[stacks 0DUH]
theorem isInvariantHom_atlasComp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : G.quotientStack ⟶ Y.toGroupoids) :
    G.IsInvariantHom (G.atlasComp f) ∧
      ∀ φ : G.U.left ⟶ Y,
        (Nonempty (G.atlas ≫ f ≅ AlgebraicSpace.toGroupoids.map φ) ↔
          φ = G.atlasComp f) :=
  sorry

/-- Lemma 106.12.2 (2). Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, and let `Y` be an algebraic
space. Every `R`-invariant morphism `φ : G.U.left ⟶ Y` arises from a unique
`2`-isomorphism class of morphisms `f : G.quotientStack ⟶ Y.toGroupoids`
factoring `G.atlas ≫ f` through `AlgebraicSpace.toGroupoids.map φ`. -/
@[stacks 0DUH]
theorem existsUnique_hom_of_isInvariantHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ) :
    ∃ f : G.quotientStack ⟶ Y.toGroupoids,
      Nonempty (G.atlas ≫ f ≅ AlgebraicSpace.toGroupoids.map φ) ∧
        (∀ g : G.quotientStack ⟶ Y.toGroupoids,
          Nonempty (G.atlas ≫ g ≅ AlgebraicSpace.toGroupoids.map φ) →
            Nonempty (f ≅ g)) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
