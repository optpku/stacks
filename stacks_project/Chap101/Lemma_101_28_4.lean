module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Composition
import StacksCheckRecall

/-!
# Composition of gerbes of algebraic stacks

If `X ⟶ Y` and `Y ⟶ Z` are morphisms of algebraic stacks, `X` is a gerbe over
`Y`, and `Y` is a gerbe over `Z`, then `X` is a gerbe over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.28.4: Let `X ⟶ Y` and `Y ⟶ Z` be morphisms of algebraic stacks.
If `X` is a gerbe over `Y` and `Y` is a gerbe over `Z`, then `X` is a gerbe
over `Z`. -/
@[stacks 06R8] #check (AlgebraicGeometry.AlgebraicStack.Gerbe.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicStack.Gerbe f] [AlgebraicStack.Gerbe g],
    AlgebraicStack.Gerbe (f ≫ g))
