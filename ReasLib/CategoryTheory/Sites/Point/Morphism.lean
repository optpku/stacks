module

public import Mathlib.CategoryTheory.Sites.Point.Category

@[expose] public section

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism from a source point to a target point is a natural transformation
from the target point's fiber functor to the source point's fiber functor. -/
abbrev Morphism (sourcePoint targetPoint : Point.{w} J) :=
  Hom sourcePoint targetPoint

end CategoryTheory.GrothendieckTopology.Point
