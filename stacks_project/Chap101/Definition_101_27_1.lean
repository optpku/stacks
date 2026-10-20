module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.27.1 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
locally of finite presentation if the equivalent conditions of Lemma 101.16.1
hold with `P` = locally of finite presentation. -/
@[stacks 06Q2] #check (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack Y] → (X ⟶ Y) → Prop)

/- Definition 101.27.1 (2): a morphism `f : X ⟶ Y` of algebraic stacks is of
finite presentation if it is locally of finite presentation, quasi-compact, and
quasi-separated. -/
@[stacks 06Q2] #check (AlgebraicGeometry.AlgebraicStack.FinitePresentation :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack Y] → (X ⟶ Y) → Prop)
