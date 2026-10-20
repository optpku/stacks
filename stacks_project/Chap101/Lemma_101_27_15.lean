module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat.Open
import StacksCheckRecall

/-!
# Flat locally of finite presentation morphisms of algebraic stacks are open on points

A morphism of algebraic stacks that is flat and locally of finite presentation
induces an open map on underlying point spaces.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 101.27.15: Let `f : X ⟶ Y` be a morphism of algebraic stacks that is
flat and locally of finite presentation. Then `|f| : |X| ⟶ |Y|` is open, i.e.
`Points.map f : Points X → Points Y` is an open map for every pair of canonical
topologies. -/
@[stacks 06R7] #check
  (AlgebraicGeometry.AlgebraicStack.Flat.pointsIsOpenMap :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f], pointsIsOpenMap f)
