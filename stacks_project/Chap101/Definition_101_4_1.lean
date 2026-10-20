module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.4.1 (1): a morphism of algebraic stacks is DM if its
relative 2-diagonal is unramified. -/
@[stacks 04YW] #check (AlgebraicGeometry.AlgebraicStack.DM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

/- Definition 101.4.1 (2): a morphism of algebraic stacks is quasi-DM if its
relative 2-diagonal is locally quasi-finite. -/
@[stacks 04YW] #check (AlgebraicGeometry.AlgebraicStack.QuasiDM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

/- Definition 101.4.1 (3): a morphism of algebraic stacks is separated if its
relative 2-diagonal is proper. -/
@[stacks 04YW] #check (AlgebraicGeometry.AlgebraicStack.Separated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

/- Definition 101.4.1 (4): a morphism of algebraic stacks is quasi-separated if
its relative 2-diagonal is quasi-compact and quasi-separated. -/
@[stacks 04YW] #check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)
