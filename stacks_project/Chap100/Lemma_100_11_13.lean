module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe.Functoriality
import StacksCheckRecall

/-!
# Functoriality of residual gerbes

A morphism of algebraic stacks sending `x` to `y` induces a 2-commutative
square between residual-gerbe inclusions at `x` and `y`, whenever those
residual gerbes exist.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

noncomputable section

universe u

/- Lemma 100.11.13: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`x ∈ |X|` with image `y ∈ |Y|`. If the residual gerbes `ιx : Zx ⟶ X` and
`ιy : Zy ⟶ Y` of `x` and `y` exist, then `f` induces a 2-commutative square
between the residual-gerbe inclusions. -/
@[stacks 0DTH] #check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.exists_map :
    ∀ {S : Scheme.{u}} {X Y Zx Zy : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Zx] [AlgebraicStack Zy]
    (f : X ⟶ Y) {x : Points X} {y : Points Y} (ιx : Zx ⟶ X) (ιy : Zy ⟶ Y)
    [IsResidualGerbe ιx x] [IsResidualGerbe ιy y],
    Points.map f x = y →
    ∃ g : Zx ⟶ Zy, Nonempty (g ≫ ιy ≅ ιx ≫ f))

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.exists_map_iff :
    ∀ {S : Scheme.{u}} {X Y Zx Zy : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Zx] [AlgebraicStack Zy]
    (f : X ⟶ Y) {x : Points X} {y : Points Y} (ιx : Zx ⟶ X) (ιy : Zy ⟶ Y)
    [IsResidualGerbe ιx x] [IsResidualGerbe ιy y],
    (∃ g : Zx ⟶ Zy, Nonempty (g ≫ ιy ≅ ιx ≫ f)) ↔ Points.map f x = y)

#check (AlgebraicGeometry.AlgebraicStack.IsResidualGerbe.map_unique :
    ∀ {S : Scheme.{u}} {X Y Zx Zy : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Zx] [AlgebraicStack Zy]
    (f : X ⟶ Y) {x : Points X} {y : Points Y} (ιx : Zx ⟶ X) (ιy : Zy ⟶ Y)
    [IsResidualGerbe ιx x] [IsResidualGerbe ιy y] (g g' : Zx ⟶ Zy),
    Nonempty (g ≫ ιy ≅ ιx ≫ f) →
    Nonempty (g' ≫ ιy ≅ ιx ≫ f) →
    Nonempty (g ≅ g'))
