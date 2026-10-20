module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

/-!
# Surjective morphisms of algebraic stacks

Typed compatibility checks for the atlas characterization of surjectivity.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Surjective :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicStack.surjective_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Surjective f ↔
      ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f))

#check (AlgebraicGeometry.AlgebraicStack.Surjective.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    Surjective (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.Surjective.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Surjective f],
    ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f))

#check (AlgebraicGeometry.AlgebraicStack.Surjective.of_groupoidsHom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Surjective f],
    Surjective f)
