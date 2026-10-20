/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Lifts

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

/-- The image of a lift object under a based functor, obtained by applying the
underlying functor to the total arrow. -/
def map (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) {x : X.p.Fiber S}
    (a : ObjectLift X.p f x) :
    ObjectLift Y.p f ((Φ.fiberFunctor S).obj x) :=
  ⟨Over.mk (Φ.map a.hom), BasedFunctor.preserves_isHomLift Φ f a.hom⟩

/-- The underlying total morphism of a mapped lift is the image of the original
total morphism. -/
theorem map_hom (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) {x : X.p.Fiber S}
    (a : ObjectLift X.p f x) : (map Φ f a).hom = Φ.map a.hom := rfl

/-- Isomorphic lift objects have isomorphic images under a based functor. -/
theorem map_preserves_iso (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) {x : X.p.Fiber S}
    {a b : ObjectLift X.p f x} (h : IsIsomorphic a b) :
    IsIsomorphic (map Φ f a) (map Φ f b) := sorry

end ObjectLift

/-- The map on isomorphism classes of lifts induced by a based functor. -/
def liftsMap (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) (x : X.p.Fiber S) :
    lifts X.p f x → lifts Y.p f ((Φ.fiberFunctor S).obj x) :=
  Quotient.map (ObjectLift.map Φ f) (fun _ _ h ↦ ObjectLift.map_preserves_iso Φ f h)

/-- `liftsMap` sends the class of a lift to the class of its image. -/
theorem liftsMap_mk (Φ : X ⥤ᵇ Y) {R S : C} (f : R ⟶ S) (x : X.p.Fiber S)
    (a : ObjectLift X.p f x) :
    liftsMap Φ f x (Quotient.mk'' a) = Quotient.mk'' (ObjectLift.map Φ f a) := rfl

end CategoryTheory.Functor
