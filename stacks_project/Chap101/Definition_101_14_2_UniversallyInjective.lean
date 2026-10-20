module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import stacks_project.Chap100.Lemma_100_4_3_Comparison

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.UniversallyInjective.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    [AlgebraicGeometry.AlgebraicStack.UniversallyInjective f]
    {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
    {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g),
    (AlgebraicGeometry.AlgebraicStack.Points.cone iso).IsBilimit →
      Function.Injective (AlgebraicGeometry.AlgebraicStack.Points.map snd))
