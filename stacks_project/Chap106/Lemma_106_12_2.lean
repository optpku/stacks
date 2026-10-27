/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallInvariant
import StacksCheckRecall

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

/- Lemma 106.12.2 (1). Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, and let `Y` be an algebraic
space. A morphism `f : SmallQuotient.quotientStack G ⟶ Y.toGroupoids` yields the
`R`-invariant morphism `G.atlasComp f : G.U.left ⟶ Y`, uniquely recovered as
the factorization of `SmallQuotient.atlas G ≫ f` through `AlgebraicSpace.toGroupoids.map`. -/
@[stacks 0DUH]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.isInvariantHom_atlasComp :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (f : SmallQuotient.quotientStack G ⟶ Y.toGroupoids),
    G.IsInvariantHom (G.atlasComp f) ∧
      ∀ φ : G.U.left ⟶ Y,
        (Nonempty (SmallQuotient.atlas G ≫ f ≅ AlgebraicSpace.toGroupoids.map φ) ↔
          φ = G.atlasComp f))

/- Lemma 106.12.2 (2). Let `G` be a groupoid in algebraic spaces with source
and target flat and locally of finite presentation, and let `Y` be an algebraic
space. Every `R`-invariant morphism `φ : G.U.left ⟶ Y` arises from a unique
`2`-isomorphism class of morphisms `f : SmallQuotient.quotientStack G ⟶ Y.toGroupoids`
factoring `SmallQuotient.atlas G ≫ f` through `AlgebraicSpace.toGroupoids.map φ`. -/
@[stacks 0DUH]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.existsUnique_hom_of_isInvariantHom :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    {Y : AlgebraicSpace S} (φ : G.U.left ⟶ Y) (hφ : G.IsInvariantHom φ),
    ∃ f : SmallQuotient.quotientStack G ⟶ Y.toGroupoids,
      Nonempty (SmallQuotient.atlas G ≫ f ≅ AlgebraicSpace.toGroupoids.map φ) ∧
        (∀ g : SmallQuotient.quotientStack G ⟶ Y.toGroupoids,
          Nonempty (SmallQuotient.atlas G ≫ g ≅ AlgebraicSpace.toGroupoids.map φ) →
            Nonempty (f ≅ g)))

end AlgebraicGeometry.GroupoidAlgebraicSpace
