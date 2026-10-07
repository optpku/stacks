module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids

/-!
# Grothendieck and discrete realizations of covariant functors

A groupoid-valued functor `C ⥤ Grpd` realizes as a category cofibered in groupoids via the
Grothendieck construction. A set-valued functor `C ⥤ Type` realizes as a category cofibered in
sets via the category of elements, and this embedding is fully faithful.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Opposite
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

/-- The Grothendieck projection associated to a groupoid-valued functor. -/
abbrev Functor.groupoidCopresheafProjection (F : C ⥤ Grpd.{vS, w}) :
    Grothendieck (F ⋙ Grpd.forgetToCat) ⥤ C :=
  Grothendieck.forget (F ⋙ Grpd.forgetToCat)

/-- The Grothendieck projection of a groupoid-valued functor is cofibered in groupoids. -/
instance Functor.groupoidCopresheafProjection.op_inGroupoids (F : C ⥤ Grpd.{vS, w}) :
    Functor.IsFibered.InGroupoids (Functor.groupoidCopresheafProjection F).op := sorry

/-- The category cofibered in groupoids associated to a functor `C ⥤ Grpd`. -/
def Functor.ofGroupoidValued (F : C ⥤ Grpd.{vS, w}) :
    CofiberedCategoryOver.Groupoids.{u, v, max u w, max v vS} C :=
  CofiberedCategoryOver.Groupoids.ofFunctor (Functor.groupoidCopresheafProjection F)

/-- The projection of `ofGroupoidValued F` is the Grothendieck forgetful functor. -/
@[simp]
theorem Functor.ofGroupoidValued.p (F : C ⥤ Grpd.{vS, w}) :
    (Functor.ofGroupoidValued F).p = Grothendieck.forget (F ⋙ Grpd.forgetToCat) := sorry

/-- An object of the Grothendieck construction is a pair `(U, x)` with `x` in `F(U)`. -/
def Functor.ofGroupoidValued.mkObj (F : C ⥤ Grpd.{vS, w}) (U : C) (x : F.obj U) :
    Grothendieck (F ⋙ Grpd.forgetToCat) :=
  ⟨U, x⟩

/-- The Grothendieck object `(U, x)` lies over `U`. -/
@[simp]
theorem Functor.ofGroupoidValued.mkObj_base (F : C ⥤ Grpd.{vS, w}) (U : C) (x : F.obj U) :
    (Functor.groupoidCopresheafProjection F).obj (Functor.ofGroupoidValued.mkObj F U x) = U := sorry

/-- A morphism `(U, x) ⟶ (V, y)` in the Grothendieck construction is a pair `(f, a)` with
`f : U ⟶ V` and `a : F(f)(x) ⟶ y` in `F(V)`. -/
def Functor.ofGroupoidValued.mkHom (F : C ⥤ Grpd.{vS, w})
    {U V : C} {x : F.obj U} {y : F.obj V}
    (f : U ⟶ V) (a : ((F ⋙ Grpd.forgetToCat).map f).toFunctor.obj x ⟶ y) :
    Functor.ofGroupoidValued.mkObj F U x ⟶ Functor.ofGroupoidValued.mkObj F V y where
  base := f
  fiber := a

/-- The covariant category-of-elements projection is a discrete fibration after passing to
opposites, i.e. a category cofibered in sets. -/
instance CategoryOfElements.π.op.isDiscreteFibration (F : C ⥤ Type w) :
    Functor.IsDiscreteFibration (CategoryOfElements.π F).op := sorry

/-- The category cofibered in groupoids associated to a functor `C ⥤ Type`. -/
def Functor.ofTypeValued (F : C ⥤ Type w) :
    CofiberedCategoryOver.Groupoids.{u, v, max u w, v} C :=
  CofiberedCategoryOver.Groupoids.ofFunctor (CategoryOfElements.π F)

/-- The projection of `ofTypeValued F` is the category-of-elements projection. -/
@[simp]
theorem Functor.ofTypeValued.p (F : C ⥤ Type w) :
    (Functor.ofTypeValued F).p = CategoryOfElements.π F := sorry

/-- The total category of `ofTypeValued F` is the category of elements of `F`. -/
@[simp]
theorem Functor.ofTypeValued.total (F : C ⥤ Type w) :
    (Functor.ofTypeValued F).total = F.Elements := sorry

/-- The category-of-elements map of a natural transformation commutes with the projections. -/
theorem Functor.ofTypeValued.map_comp_p {F G : C ⥤ Type w} (α : F ⟶ G) :
    CategoryOfElements.map α ⋙ CategoryOfElements.π G = CategoryOfElements.π F := sorry

/-- A natural transformation of set-valued functors induces a morphism of the associated
categories cofibered in groupoids. -/
def Functor.ofTypeValuedMap {F G : C ⥤ Type w} (α : F ⟶ G) :
    Functor.ofTypeValued F ⟶ Functor.ofTypeValued G :=
  CofiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedFunctor.ofFunctor (CategoryOfElements.map α) (CategoryOfElements.map_π α))

/-- The total functor of `ofTypeValuedMap α` is the category-of-elements map of `α`. -/
@[simp]
theorem Functor.ofTypeValuedMap.toFunctor {F G : C ⥤ Type w} (α : F ⟶ G) :
    CofiberedCategoryOver.Groupoids.toFunctor (Functor.ofTypeValuedMap α) =
      CategoryOfElements.map α := sorry

/-- The image of `(U, x)` under a morphism of associated cofibered categories still lies over `U`. -/
def Functor.ofTypeValued.mappedBase {F G : C ⥤ Type w}
    (φ : Functor.ofTypeValued F ⟶ Functor.ofTypeValued G)
    {U : C} (x : F.obj U) :
    ((CofiberedCategoryOver.Groupoids.toFunctor φ).obj ⟨U, x⟩).1 = U :=
  congrFun (congrArg Functor.obj
    (CofiberedCategoryOver.Groupoids.toBasedFunctor φ).w) ⟨U, x⟩

/-- Recover a natural transformation from a morphism of associated cofibered categories. -/
def Functor.ofTypeValued.preimage {F G : C ⥤ Type w}
    (φ : Functor.ofTypeValued F ⟶ Functor.ofTypeValued G) : F ⟶ G where
  app U := TypeCat.ofHom fun (x : F.obj U) =>
    let fx := (CofiberedCategoryOver.Groupoids.toFunctor φ).obj ⟨U, x⟩
    (ConcreteCategory.hom (G.map (eqToHom (Functor.ofTypeValued.mappedBase φ x)))) fx.2
  naturality := sorry

/-- The discrete embedding of `C ⥤ Type` into categories cofibered in groupoids over `C`. -/
def Functor.ofTypeValuedFunctor :
    (C ⥤ Type w) ⥤ CofiberedCategoryOver.Groupoids.{u, v, max u w, v} C where
  obj := Functor.ofTypeValued
  map := Functor.ofTypeValuedMap
  map_id := sorry
  map_comp := sorry

/-- Applying `ofTypeValuedMap` and then `preimage` recovers the original natural transformation. -/
theorem Functor.ofTypeValued.preimage_map {F G : C ⥤ Type w} (α : F ⟶ G) :
    Functor.ofTypeValued.preimage (Functor.ofTypeValuedMap α) = α := sorry

/-- Applying `preimage` and then `ofTypeValuedMap` recovers the original cofibered morphism. -/
theorem Functor.ofTypeValued.map_preimage {F G : C ⥤ Type w}
    (φ : Functor.ofTypeValued F ⟶ Functor.ofTypeValued G) :
    Functor.ofTypeValuedMap (Functor.ofTypeValued.preimage φ) = φ := sorry

/-- The discrete embedding is fully faithful on hom-sets. -/
theorem Functor.ofTypeValuedMap.bijective {F G : C ⥤ Type w} :
    Function.Bijective
      (Functor.ofTypeValuedMap : (F ⟶ G) →
        (Functor.ofTypeValued F ⟶ Functor.ofTypeValued G)) := sorry

end CategoryTheory
