module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe

/-!
# Functoriality of residual gerbes

A morphism of algebraic stacks sending `x` to `y` induces a 2-commutative
square between residual-gerbe inclusions at `x` and `y`, whenever those
residual gerbes exist.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsResidualGerbe

/-- A morphism of algebraic stacks carrying `x` to `y` admits a morphism
between their residual gerbes whose square with the inclusions commutes up to
2-isomorphism. -/
@[stacks 0DTH]
theorem exists_map {S : Scheme.{u}} {X Y Zx Zy : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Zx] [AlgebraicStack Zy]
    (f : X ⟶ Y) {x : Points X} {y : Points Y} (ιx : Zx ⟶ X) (ιy : Zy ⟶ Y)
    [IsResidualGerbe ιx x] [IsResidualGerbe ιy y]
    (h_image : Points.map f x = y) :
    ∃ g : Zx ⟶ Zy, Nonempty (g ≫ ιy ≅ ιx ≫ f) :=
  sorry

/-- A morphism of algebraic stacks 2-commutes with residual-gerbe inclusions at
`x` and `y` if and only if it sends `x` to `y`. -/
theorem exists_map_iff {S : Scheme.{u}} {X Y Zx Zy : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Zx] [AlgebraicStack Zy]
    (f : X ⟶ Y) {x : Points X} {y : Points Y} (ιx : Zx ⟶ X) (ιy : Zy ⟶ Y)
    [IsResidualGerbe ιx x] [IsResidualGerbe ιy y] :
    (∃ g : Zx ⟶ Zy, Nonempty (g ≫ ιy ≅ ιx ≫ f)) ↔ Points.map f x = y :=
  sorry

/-- Residual-gerbe liftings of a morphism of algebraic stacks are unique up to
2-isomorphism. -/
theorem map_unique {S : Scheme.{u}} {X Y Zx Zy : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Zx] [AlgebraicStack Zy]
    (f : X ⟶ Y) {x : Points X} {y : Points Y} (ιx : Zx ⟶ X) (ιy : Zy ⟶ Y)
    [IsResidualGerbe ιx x] [IsResidualGerbe ιy y] (g g' : Zx ⟶ Zy)
    (hg : Nonempty (g ≫ ιy ≅ ιx ≫ f))
    (hg' : Nonempty (g' ≫ ιy ≅ ιx ≫ f)) :
    Nonempty (g ≅ g') :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsResidualGerbe
