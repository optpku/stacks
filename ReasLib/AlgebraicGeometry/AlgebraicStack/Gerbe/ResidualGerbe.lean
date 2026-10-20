module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Residual gerbes of gerbe algebraic stacks

Every point of a gerbe algebraic stack admits a residual gerbe.
Residual gerbes are preserved by base change along gerbe morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Every point of a gerbe algebraic stack admits a residual gerbe. -/
@[stacks 06RA]
instance instHasResidualGerbe_of_isGerbe {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsGerbe X] (x : Points X) :
    HasResidualGerbe X x :=
  sorry

namespace IsResidualGerbe

/-- Pulling back a residual-gerbe inclusion at the image of a point along a gerbe
morphism of algebraic stacks gives a residual gerbe at that point, with inclusion
given by the second projection of the 2-fibre product. -/
@[stacks 0H24]
instance of_gerbe {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (π : X ⟶ Y) [Gerbe π] (ι : Z ⟶ Y) {x : Points X}
    [IsResidualGerbe ι (Points.map π x)] :
    IsResidualGerbe (TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι π) x :=
  sorry

/-- If `X` is a gerbe over `Y` and `Y` has a residual gerbe at the image of
`x ∈ |X|`, then the residual gerbe of `X` at `x` exists. -/
theorem hasResidualGerbe {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (π : X ⟶ Y) [Gerbe π] (ι : Z ⟶ Y) {x : Points X} {y : Points Y}
    [IsResidualGerbe ι y] (hy : Points.map π x = y) :
    HasResidualGerbe X x :=
  sorry

/-- If `X` is a gerbe algebraic stack, then there is a residual gerbe of `X` at
every point `x ∈ |X|`. -/
theorem exists_at_of_isGerbe {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsGerbe X] (x : Points X) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (ι : Z ⟶ X),
      IsResidualGerbe ι x :=
  ⟨residualGerbe X x, instAlgebraicStack_residualGerbe X x,
    residualGerbeι X x, instIsResidualGerbe_residualGerbeι X x⟩

end IsResidualGerbe

end AlgebraicGeometry.AlgebraicStack
