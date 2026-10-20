module

public import Mathlib.CategoryTheory.Sites.Point.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory GrothendieckTopology

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Definition 7.37.2: on a site C, a morphism f : p ⟶ p' of points given by
functors u, u' : C ⥤ Type is a natural transformation f_u : u' ⟶ u.

`GrothendieckTopology.Point.Hom` is mathlib's morphism of points: a morphism
`p ⟶ p'` is a natural transformation from the fiber functor of `p'` to the
fiber functor of `p`, i.e. in the opposite direction. -/
@[stacks 00YI] #check (CategoryTheory.GrothendieckTopology.Point.Hom :
  Point.{w} J → Point.{w} J → Type (max u w))

variable {sourcePoint targetPoint : Point.{w} J}

#check (CategoryTheory.GrothendieckTopology.Point.Hom.hom :
  Point.Hom sourcePoint targetPoint → (targetPoint.fiber ⟶ sourcePoint.fiber))

#check (CategoryTheory.GrothendieckTopology.Point.Hom.mk :
  (targetPoint.fiber ⟶ sourcePoint.fiber) → Point.Hom sourcePoint targetPoint)
