module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Submersive
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.12.2 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
submersive if the continuous map `|X| ⟶ |Y|` is a quotient map. -/
@[stacks 06U6] #check (AlgebraicGeometry.AlgebraicStack.Submersive :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

/- Definition 101.12.2 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
universally submersive if for every morphism of algebraic stacks `Z ⟶ Y` the
base change `Z ×_Y X ⟶ Z` is submersive. -/
@[stacks 06U6] #check (AlgebraicGeometry.AlgebraicStack.UniversallySubmersive :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)
