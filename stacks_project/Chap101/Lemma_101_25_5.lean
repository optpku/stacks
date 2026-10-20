module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat.Descent
import StacksCheckRecall

/-!
# Permanence of flatness for morphisms of algebraic stacks

If `X ⟶ Z` is flat and `X ⟶ Y` is surjective and flat, then `Y ⟶ Z` is
flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.25.5: Let `X ⟶ Y ⟶ Z` be morphisms of algebraic stacks. If
`X ⟶ Z` is flat and `X ⟶ Y` is surjective and flat, then `Y ⟶ Z` is
flat. -/
@[stacks 06Q0] #check (AlgebraicGeometry.AlgebraicStack.Flat.of_comp_surjective_flat :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicStack.Flat (f ≫ g)] [AlgebraicStack.Flat f]
    [AlgebraicStack.Surjective f], AlgebraicStack.Flat g)
