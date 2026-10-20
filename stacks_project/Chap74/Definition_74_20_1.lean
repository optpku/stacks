module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 74.20.1: for a scheme `S` and a property `P` of morphisms of algebraic
spaces over `S`, `P` is smooth local on source-and-target when it is stable under
precomposition with smooth maps, stable under smooth base change, and a morphism
`f : X ⟶ Y` has `P` if and only if every point of `|X|` lies under a commutative
square with smooth vertical arrows whose top arrow has `P`. -/
@[stacks 06F8] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget :
    {S : AlgebraicGeometry.Scheme.{u}} →
      CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S) → Prop)
