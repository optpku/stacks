module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 76.14.1: Let `S` be a scheme. A morphism `f : X ⟶ Y` of algebraic
spaces over `S` is said to be formally unramified if it is formally unramified as a
transformation of functors as in Definition 76.13.1. -/
@[stacks 04G7]
#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)
