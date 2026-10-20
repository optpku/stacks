module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 96.4.1: the associated topology on a category fibred in groupoids
is inherited from the selected big topology on `(Sch/S)`. -/
@[stacks 06TP] #check (AlgebraicGeometry.GroupoidsOver.associatedTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    (τ : AlgebraicGeometry.StandardTopology), GrothendieckTopology X.total)
