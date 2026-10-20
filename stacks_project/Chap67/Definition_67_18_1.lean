module

public import stacks_project.Chap67.Definition_67_18_1_Dominant
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 67.18.1: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
dominant if the image of `Points.map f : |X| ⟶ |Y|` is dense in `|Y|`. -/
@[stacks 0ABL] #check (AlgebraicGeometry.AlgebraicSpace.Dominant :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X Y : AlgebraicGeometry.AlgebraicSpace S} → (X ⟶ Y) → Prop)
