module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber actions of morphisms of fibred categories

This leaf exposes the action of morphisms and `2`-morphisms in
`FiberedCategoryOver C` on total categories and standard fibers.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w vS

namespace CategoryTheory

open BasedFunctor
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver

variable {X Y : FiberedCategoryOver C}

/-- The underlying based functor of a morphism of fibred categories over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  F.obj

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  toBasedFunctor F |>.fiberFunctor U

/-- The underlying functor between total categories. -/
abbrev toFunctor (F : X ⟶ Y) : X.total ⥤ Y.total :=
  toBasedFunctor F |>.toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p :=
  toBasedFunctor F |>.w

/-- The total-category functor underlying the identity morphism of a fibred category is the
identity functor. -/
@[simp]
theorem toFunctor.id (X : FiberedCategoryOver C) :
    toFunctor (𝟙 X) = 𝟭 X.total := sorry

/-- Passing to total-category functors preserves composition of morphisms of fibred
categories. -/
@[simp]
theorem toFunctor.comp
    {Z : FiberedCategoryOver C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toFunctor (F ≫ G) = toFunctor F ⋙ toFunctor G := sorry

/-- The underlying total-category object of a fiber-functor image is the image under the
underlying morphism of fibred categories. -/
@[simp]
theorem fiberFunctor.obj.val (F : X ⟶ Y) (U : C) (x : X.p.Fiber U) :
    ((fiberFunctor F U).obj x).1 = (toFunctor F).obj x.1 := sorry

/-- The underlying total-category morphism of a fiber-functor image is the image under the
underlying morphism of fibred categories. -/
@[simp]
theorem fiberFunctor.map.val (F : X ⟶ Y) (U : C)
    {x y : X.p.Fiber U} (φ : x ⟶ y) :
    ((fiberFunctor F U).map φ).1 = (toFunctor F).map φ.1 := sorry

/-- The identity morphism of a fibred category restricts to the identity on every standard
fiber. -/
@[simp]
theorem fiberFunctor.id (X : FiberedCategoryOver.{u, v, w, vS} C) (U : C) :
    fiberFunctor (𝟙 X) U = 𝟭 (X.p.Fiber U) := sorry

/-- A composite of morphisms of fibred categories restricts to the composite of their standard
fiber functors. -/
@[simp]
theorem fiberFunctor.comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) (U : C) :
    fiberFunctor (F ≫ G) U = fiberFunctor F U ⋙ fiberFunctor G U := sorry

/-- A `2`-morphism of fibred-category morphisms restricts to a natural transformation on every
standard fiber. This construction depends only on the standard fibers, not on a choice of
cleavage. -/
def fiberNatTrans {F G : X ⟶ Y} (τ : F ⟶ G) (U : C) :
    fiberFunctor F U ⟶ fiberFunctor G U :=
  BasedNatTrans.fiber τ.hom U

/-- The component of a restricted owner `2`-morphism is the canonical fiber component of its
underlying based natural transformation. -/
@[simp]
theorem fiberNatTrans.app {F G : X ⟶ Y} (τ : F ⟶ G) (U : C)
    (x : X.p.Fiber U) :
    (fiberNatTrans τ U).app x = BasedNatTrans.fiberApp τ.hom U x := sorry

/-- Forgetting a restricted owner `2`-morphism to the total category recovers its original
component. -/
@[simp]
theorem fiberNatTrans.app.val {F G : X ⟶ Y} (τ : F ⟶ G) (U : C)
    (x : X.p.Fiber U) :
    ((fiberNatTrans τ U).app x).1 = τ.hom.toNatTrans.app x.1 := sorry

/-- Naturality of an owner `2`-morphism after restriction to a standard fiber. -/
@[reassoc]
theorem fiberNatTrans.naturality
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : C)
    {x y : X.p.Fiber U} (φ : x ⟶ y) :
    (fiberFunctor F U).map φ ≫ (fiberNatTrans τ U).app y =
      (fiberNatTrans τ U).app x ≫ (fiberFunctor G U).map φ := sorry

/-- A restricted owner `2`-morphism component transports by conjugation along an isomorphism
in the source fiber. -/
theorem fiberNatTrans.app.transport
    {F G : X ⟶ Y} (τ : F ⟶ G) (U : C)
    {x y : X.p.Fiber U} (e : x ≅ y) :
    (fiberNatTrans τ U).app y =
      (fiberFunctor F U).map e.inv ≫
        (fiberNatTrans τ U).app x ≫
        (fiberFunctor G U).map e.hom := sorry

/-- Restriction of the identity owner `2`-morphism to a standard fiber is the identity natural
transformation. -/
@[simp]
theorem fiberNatTrans.id (F : X ⟶ Y) (U : C) :
    fiberNatTrans (𝟙 F) U = 𝟙 (fiberFunctor F U) := sorry

/-- Restriction to a standard fiber preserves vertical composition of owner `2`-morphisms. -/
@[simp]
theorem fiberNatTrans.comp
    {F G H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) (U : C) :
    fiberNatTrans (τ ≫ σ) U =
      fiberNatTrans τ U ≫ fiberNatTrans σ U := sorry

/-- Evaluation on the standard fiber over `U`, functorial in morphisms and `2`-morphisms of
fibred categories. This is the hom-category-level owner of fiber restriction. -/
def fiberHomFunctor
    (X Y : FiberedCategoryOver.{u, v, w, vS} C) (U : C) :
    (X ⟶ Y) ⥤ (X.p.Fiber U ⥤ Y.p.Fiber U) where
  obj F := fiberFunctor F U
  map τ := fiberNatTrans τ U
  map_id F := fiberNatTrans.id F U
  map_comp τ σ := fiberNatTrans.comp τ σ U

/-- The object map of `fiberHomFunctor` is restriction of a fibred-category morphism to the
standard fiber. -/
@[simp]
theorem fiberHomFunctor.obj
    {X Y : FiberedCategoryOver.{u, v, w, vS} C} (U : C) (F : X ⟶ Y) :
    (fiberHomFunctor X Y U).obj F = fiberFunctor F U := sorry

/-- The morphism map of `fiberHomFunctor` is restriction of an owner `2`-morphism to the
standard fiber. -/
@[simp]
theorem fiberHomFunctor.map
    {X Y : FiberedCategoryOver.{u, v, w, vS} C} (U : C)
    {F G : X ⟶ Y} (τ : F ⟶ G) :
    (fiberHomFunctor X Y U).map τ = fiberNatTrans τ U := sorry

end FiberedCategoryOver

end CategoryTheory
