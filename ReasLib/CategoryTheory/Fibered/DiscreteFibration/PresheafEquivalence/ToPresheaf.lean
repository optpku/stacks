/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
public import ReasLib.CategoryTheory.Fibered.InSets.Hom
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.FiberObject.Map

/-!
# Straightening discrete fibrations

This leaf packages fiber-object presheaves into the functor from categories
fibred in sets to set-valued presheaves and exposes its pointwise API.
-/

@[expose] public section

universe w u v uS vS

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

variable (C) in
/-- Straightening for discrete fibrations: a category fibred in sets is sent to its presheaf of
fiber objects, and a morphism over `C` acts by its induced fiberwise object functions. The base
category is explicit because this global functor has no value input from which Lean can recover it. -/
@[stacks 02Y2 "straightening discrete fibrations"]
noncomputable def toPresheaf :
    FiberedCategoryOver.Sets C ⥤ (Cᵒᵖ ⥤ Type uS) where
  obj X := X.p.fiberObjectPresheaf
  map F := (toBasedFunctor F).fiberObjectMap
  map_id _ := sorry
  map_comp _ _ := sorry

/- Axiom audit: object and component functions are explicit. The `sorryAx` dependency is confined
to naturality and functor-law proofs. -/

/-- Straightening sends a discrete fibration to its canonical presheaf of fiber objects. -/
@[simp]
theorem toPresheaf.obj (X : FiberedCategoryOver.Sets C) :
    (toPresheaf C).obj X = X.p.fiberObjectPresheaf := sorry
/- Proof strategy: unfold only the object projection of `toPresheaf`. -/

/-- On each base object, the map produced by straightening is the object function of the induced
fiber functor. -/
@[simp]
theorem toPresheaf.map.app
    {X Y : FiberedCategoryOver.Sets C} (F : X ⟶ Y) (U : Cᵒᵖ) :
    ((toPresheaf C).map F).app U =
      TypeCat.ofHom (fiberFunctor F (unop U)).obj := sorry
/- Proof strategy: unfold the map and component projections of `toPresheaf`; it delegates to
`BasedFunctor.fiberObjectMap`, whose component stores exactly this object function. -/

/-- Pointwise, straightening maps a fiber object by the induced fiber functor. -/
@[simp]
theorem toPresheaf.map.app_apply
    {X Y : FiberedCategoryOver.Sets C} (F : X ⟶ Y) (U : Cᵒᵖ)
    (x : X.p.Fiber (unop U)) :
    ((toPresheaf C).map F).app U x =
      (fiberFunctor F (unop U)).obj x := sorry
/- Proof strategy: apply `toPresheaf.map.app` and evaluate `TypeCat.ofHom`. -/

/-- Pointwise naturality of straightening: mapping an intrinsically reindexed fiber object is
intrinsic reindexing of its image. This is the strict equality obtained from uniqueness of lifts;
general fibred categories only admit the analogous comparison up to isomorphism. -/
@[simp]
theorem toPresheaf.map.reindexObj
    {X Y : FiberedCategoryOver.Sets C} (F : X ⟶ Y)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : X.p.Fiber (unop U)) :
    (fiberFunctor F (unop V)).obj
        (Functor.IsDiscreteFibration.reindexObj X.p f.unop x) =
      Functor.IsDiscreteFibration.reindexObj Y.p f.unop
        ((fiberFunctor F (unop U)).obj x) := sorry
/- Proof strategy: evaluate the naturality equation of `(toPresheaf C).map F` at `x`,
then rewrite its two restriction maps by `fiberObjectPresheaf.map_apply` and its two components by
`toPresheaf.map.app_apply`. -/

end FiberedCategoryOver.Sets

end CategoryTheory
