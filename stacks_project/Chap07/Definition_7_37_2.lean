module

public import Mathlib.CategoryTheory.Sites.Point.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory GrothendieckTopology

/- Definition 7.37.2: on a site C, a morphism f : p ⟶ p' of points given by
functors u, u' : C ⥤ Type is a natural transformation f_u : u' ⟶ u.

The canonical owner is `GrothendieckTopology.Point.Hom`: a morphism Φ₁ ⟶ Φ₂ is
a natural transformation Φ₂.fiber ⟶ Φ₁.fiber, opposite to the morphism of
points. -/
@[stacks 00YI] #check @Point.Hom

#check @Point.Hom.hom
