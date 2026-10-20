module

public import ReasLib.AlgebraicGeometry.AwayTwo
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Exercise 111.33.8: the morphism from the open subscheme `D(2) ⊆ Spec ℤ` to
`Spec (Localization.Away (2 : ℤ))` does not extend along the open-subscheme
inclusion to a morphism `Spec ℤ ⟶ Spec (Localization.Away (2 : ℤ))`. -/
@[stacks 028U] #check (AlgebraicGeometry.AwayTwo.morphism_not_extends :
  ¬ ∃ g : AlgebraicGeometry.AwayTwo.source ⟶ AlgebraicGeometry.AwayTwo.target,
    AlgebraicGeometry.AwayTwo.openSubscheme.ι ≫ g = AlgebraicGeometry.AwayTwo.morphism)
