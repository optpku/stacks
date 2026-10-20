module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 76.55.1: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is at-worst-nodal of relative dimension 1 if the equivalent conditions of Lemma 67.22.1
hold with `P` = at-worst-nodal of relative dimension 1. -/
@[stacks 0DSE] #check (AlgebraicGeometry.AlgebraicSpace.AtWorstNodal :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
