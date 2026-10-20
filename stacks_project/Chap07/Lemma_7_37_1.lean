module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Fiber.Map

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {p p' : GrothendieckTopology.Point.{v} J} (f : p ⟶ p')
variable (U X : C) (x : p'.fiber.obj X)

/- Lemma 7.37.1 (00YH): the component of the map on sheaf fibers induced by a
morphism of points is the component of its map on the underlying presheaf fibers. -/
@[stacks 00YH] #check Hom.sheafFiber_app (A := Type v) f

/- Lemma 7.37.1 (00YH): on a representable presheaf, the map induced by a
morphism of points sends each canonical fiber generator to the generator indexed
by its image under `f.hom`. -/
@[stacks 00YH] #check Hom.toPresheafFiber_app
  (A := Type v) f (CategoryTheory.yoneda.obj U) X x

end CategoryTheory.GrothendieckTopology.Point
