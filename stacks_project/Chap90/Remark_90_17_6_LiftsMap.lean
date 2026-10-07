module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import stacks_project.Chap90.Definition_90_17_1_ObjectLift

/-!
# Induced maps on lift objects and lift classes

A based functor `Φ : X ⥤ᵇ Y` sends a lift of `x` along `f` to a lift of
`Φ(x)` along the same base arrow, by applying the underlying functor to the
total morphism. This induces a map on isomorphism classes of lifts.
-/

@[expose] public section

open CategoryTheory
open Functor Fiber BasedFunctor
open scoped Bicategory

universe u v uX vX uY vY

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

namespace CategoryTheory.Functor

namespace ObjectLift

/-- A based functor sends a total arrow lying over `f` to a total arrow lying over
`f`. -/
instance instIsHomLift_map (Φ : X ⥤ᵇ Y) {R S : C} {f : R ⟶ S} {x : X.p.Fiber S}
    (a : ObjectLift X.p f x) : Y.p.IsHomLift f (Φ.map a.hom) := sorry

/-- The image of a lift object under a based functor, obtained by applying the
underlying functor to the total arrow. -/
def map (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) {x : X.p.Fiber S}
    (a : ObjectLift X.p f x) :
    ObjectLift Y.p f ((Φ.fiberFunctor S).obj x) :=
  ⟨Over.mk (Φ.map a.hom), sorry⟩

/-- The underlying total morphism of a mapped lift is the image of the original
total morphism. -/
theorem map_hom (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) {x : X.p.Fiber S}
    (a : ObjectLift X.p f x) : (map Φ f a).hom = Φ.map a.hom := sorry

end ObjectLift

/-- The map on isomorphism classes of lifts induced by a based functor. -/
def liftsMap (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) (x : X.p.Fiber S) :
    lifts X.p f x → lifts Y.p f ((Φ.fiberFunctor S).obj x) :=
  Quotient.lift (fun a ↦ Quotient.mk'' (ObjectLift.map Φ f a)) sorry

/-- `liftsMap` sends the class of a lift to the class of its image. -/
theorem liftsMap_mk (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) (x : X.p.Fiber S)
    (a : ObjectLift X.p f x) :
    liftsMap Φ f x (Quotient.mk'' a) = Quotient.mk'' (ObjectLift.map Φ f a) := sorry

end CategoryTheory.Functor
