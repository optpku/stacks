module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

universe u

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme morphism is flat when its canonical flatness predicate holds. -/
def isFlatMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop := Flat f

end AlgebraicGeometry
