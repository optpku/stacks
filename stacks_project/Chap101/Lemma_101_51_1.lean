module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.ResidualGerbe
import StacksCheckRecall

/-!
# Residual gerbes of gerbes of algebraic stacks

If `π : X ⟶ Y` is a gerbe of algebraic stacks and the residual gerbe of `Y` at
the image of `x ∈ |X|` exists, then the 2-fibre product of that residual gerbe
with `X` is a residual gerbe of `X` at `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.51.1: Let `π : X ⟶ Y` be a morphism of algebraic stacks. Let
`x ∈ |X|` with image `y ∈ |Y|`. Assume the residual gerbe `Z_y ⊂ Y` of `Y` at
`y` exists and that `X` is a gerbe over `Y`. Then `Z_x = Z_y ×_Y X` is the
residual gerbe of `X` at `x`.

Here `Z_y ×_Y X` is `TwoFibreProduct.apex ι π` for a residual-gerbe
monomorphism `ι : Z ⟶ Y` at `y`, and the inclusion `Z_x ⟶ X` is
`TwoFibreProduct.snd ι π`. -/
@[stacks 0H24]
#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.of_gerbe :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (π : X ⟶ Y) [Gerbe π] (ι : Z ⟶ Y) {x : Points X}
    [IsResidualGerbe ι (Points.map π x)],
    IsResidualGerbe (TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι π) x)

/- If `X` is a gerbe over `Y` and `Y` has a residual gerbe at the image of
`x ∈ |X|`, then the residual gerbe of `X` at `x` exists. -/
#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.hasResidualGerbe :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (π : X ⟶ Y) [Gerbe π] (ι : Z ⟶ Y) {x : Points X} {y : Points Y}
    [IsResidualGerbe ι y] (hy : Points.map π x = y),
    HasResidualGerbe X x)

end AlgebraicGeometry.AlgebraicStack
