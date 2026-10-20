module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.11.2 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
open if the map of topological spaces `|X| ⟶ |Y|` is open. -/
@[stacks 06U2] #check (AlgebraicGeometry.AlgebraicStack.Open :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack Y] → (X ⟶ Y) → Prop)

/- Definition 101.11.2 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
universally open if for every morphism of algebraic stacks `Z ⟶ Y` the map
`|Z ×_Y X| ⟶ |Z|` is open, i.e. the base change `Z ×_Y X ⟶ Z` is open. -/
@[stacks 06U2] #check (AlgebraicGeometry.AlgebraicStack.UniversallyOpen :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack Y] → (X ⟶ Y) → Prop)
