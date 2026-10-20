module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 76.16.1: Let `S` be a scheme. A morphism `f : X ⟶ Y` of algebraic
spaces over `S` is said to be formally étale if it is formally étale as a
transformation of functors as in Definition 76.13.1. -/
@[stacks 04GC]
#check (AlgebraicGeometry.AlgebraicSpace.FormallyEtale :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)
