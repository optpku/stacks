/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Surjective morphisms of algebraic stacks

A morphism of algebraic stacks is surjective in the atlas form of
Definition 100.5.1: some scheme atlas of the source remains surjective after
composition. This is equivalent to the induced map of associated topological
spaces being surjective, and it does not require the morphism itself to be
representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is surjective if some scheme atlas of the
source is surjective and remains surjective after composition. Equivalently,
the induced map of associated topological spaces is surjective. -/
class Surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a scheme `U` over `S` and a surjective 1-morphism
  `a : GroupoidsOver.slice U ⟶ X` such that `a ≫ f` is also surjective. -/
  exists_surjective_scheme_atlas :
    ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f)

/-- A morphism of algebraic stacks is surjective if and only if some scheme
atlas of the source is surjective and remains surjective after composition. -/
theorem surjective_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Surjective f ↔
      ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f) :=
  sorry

namespace Surjective

/-- The identity morphism of an algebraic stack is surjective. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Surjective (𝟙 X) :=
  sorry

/-- A surjective morphism of algebraic stacks admits a scheme atlas of the
source that remains surjective after composition. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Surjective f] :
    ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f) :=
  sorry

/-- A 1-morphism of algebraic stacks which is surjective in the sense of
relative representability by algebraic spaces is surjective as a morphism of
algebraic stacks. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Surjective f] : Surjective f :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicStack
