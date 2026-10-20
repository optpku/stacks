/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presheaves on fibers of a fibered category

This file owns the coefficient-independent restriction and reindexing operations for presheaves
on the total category of a fibered category.  The optional bundled projective-preservation
interface lives in `ReasLib.CategoryTheory.Fibered.Presheaf.Projective`.
-/

@[expose] public section

open CategoryTheory Opposite Functor.Fiber

noncomputable section

universe u v w vS a b

namespace CategoryTheory.FiberedCategoryOver.Presheaf

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver.{u, v, w, vS} C)
variable (A : Type a) [Category.{b} A]

/-- Restriction of a presheaf on the total category to the fiber over `U`. -/
@[stacks 08PE "presheaf restriction to a fiber"]
abbrev restrict (F : X.totalᵒᵖ ⥤ A) (U : C) : (X.p.Fiber U)ᵒᵖ ⥤ A :=
  (fiberInclusion (p := X.p) (S := U)).op ⋙ F

/-- Restriction sends a coefficient natural transformation to its fiberwise component. -/
@[stacks 08PE "presheaf restriction of coefficient morphisms"]
abbrev restrictMap {F G : X.totalᵒᵖ ⥤ A} (τ : F ⟶ G) (U : C) :
    restrict X A F U ⟶ restrict X A G U :=
  Functor.whiskerLeft
    ((fiberInclusion (p := X.p) (S := U)).op) τ

/-- Precomposition of fiber presheaves along the cleavage reindexing over `f`. -/
@[stacks 08PE "fiber-presheaf reindexing"]
abbrev reindex {U V : C} (f : V ⟶ U) :
    ((X.p.Fiber V)ᵒᵖ ⥤ A) ⥤ ((X.p.Fiber U)ᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft (X.p.Fiber U)ᵒᵖ (X.p.Fiber V)ᵒᵖ A).obj
    ((Functor.Cleavage.ofIsFibered X.p).reindex f).op

/-- The comparison isomorphism between composite fiber reindexing and reindexing along a
composite base arrow. -/
@[stacks 08PE "fiber reindexing composition isomorphism"]
noncomputable def reindexCompIso {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (reindex X A g) ⋙ (reindex X A f) ≅ reindex X A (g ≫ f) :=
  (Functor.whiskeringLeft (X.p.Fiber U)ᵒᵖ (X.p.Fiber W)ᵒᵖ A).mapIso
    (NatIso.op (Functor.Cleavage.Reindex.compIso
      (Functor.Cleavage.ofIsFibered X.p) f g))

/-- The identity reindexing functor is naturally isomorphic to the identity functor on fiber
presheaves. -/
@[stacks 08PE "fiber-presheaf identity reindexing isomorphism"]
noncomputable def reindexIdIso {U : C} :
    reindex X A (𝟙 U) ≅ 𝟭 ((X.p.Fiber U)ᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft (X.p.Fiber U)ᵒᵖ (X.p.Fiber U)ᵒᵖ A).mapIso
    (NatIso.op (Functor.Cleavage.Reindex.idIso
      (Functor.Cleavage.ofIsFibered X.p) U))

/-- The component of the cartesian restriction map at a fiber object. -/
@[stacks 08PE "cartesian restriction component"]
abbrev cartesianRestrictionApp
    (F : X.totalᵒᵖ ⥤ A) {U V : C} (f : V ⟶ U)
    (x : (X.p.Fiber U)ᵒᵖ) :
    (restrict X A F U).obj x ⟶ ((reindex X A f).obj (restrict X A F V)).obj x :=
  F.map (op ((Functor.Cleavage.ofIsFibered X.p).cartesianHom f x.unop))

/-- Naturality of the cartesian restriction components in the source fiber. -/
@[stacks 08PE "cartesian restriction naturality"]
theorem cartesianRestriction_naturality
    (F : X.totalᵒᵖ ⥤ A) {U V : C} (f : V ⟶ U) :
    ∀ {x y : (X.p.Fiber U)ᵒᵖ} (g : x ⟶ y),
      (restrict X A F U).map g ≫ cartesianRestrictionApp X A F f y =
        cartesianRestrictionApp X A F f x ≫
          ((reindex X A f).obj (restrict X A F V)).map g := sorry

/-- The natural transformation from restriction over `U` to the reindexed restriction over `V`. -/
@[stacks 08PE "cartesian restriction natural transformation"]
def cartesianRestriction
    (F : X.totalᵒᵖ ⥤ A) {U V : C} (f : V ⟶ U) :
    restrict X A F U ⟶ (reindex X A f).obj (restrict X A F V) where
  app x := cartesianRestrictionApp X A F f x
  naturality := fun {_ _} g ↦ cartesianRestriction_naturality X A F f g

/-- Restriction maps of coefficients commute with cartesian reindexing. -/
@[stacks 08PE "cartesian restriction naturality in coefficients"]
theorem cartesianRestriction_naturality_map
    {F G : X.totalᵒᵖ ⥤ A} (τ : F ⟶ G) {U V : C} (f : V ⟶ U) :
    restrictMap X A τ U ≫ cartesianRestriction X A G f =
      cartesianRestriction X A F f ≫
        (reindex X A f).map (restrictMap X A τ V) := sorry

/-- The canonical restriction map over an identity base arrow. -/
@[stacks 08PE "cartesian restriction identity comparison"]
noncomputable def cartesianRestrictionId (F : X.totalᵒᵖ ⥤ A) (U : C) :
    restrict X A F U ⟶ (reindex X A (𝟙 U)).obj (restrict X A F U) :=
  Functor.whiskerRight
    (NatTrans.op ((Functor.Cleavage.Reindex.idIso
      (Functor.Cleavage.ofIsFibered X.p) U).inv))
    (restrict X A F U)

/-- The identity cartesian restriction is the inverse component of `reindexIdIso`. -/
@[stacks 08PE "cartesian restriction identity isomorphism bridge"]
theorem cartesianRestrictionId_eq
    (F : X.totalᵒᵖ ⥤ A) (U : C) :
    cartesianRestrictionId X A F U =
      (reindexIdIso X A (U := U)).inv.app (restrict X A F U) := sorry

/-- The canonical restriction map over a composite base arrow, expressed through the reindexing
composition isomorphism. -/
@[stacks 08PE "cartesian restriction composition comparison"]
noncomputable def cartesianRestrictionComp
    (F : X.totalᵒᵖ ⥤ A) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restrict X A F U ⟶ (reindex X A (g ≫ f)).obj (restrict X A F W) :=
  cartesianRestriction X A F f ≫
    (reindex X A f).map (cartesianRestriction X A F g) ≫
      (reindexCompIso X A f g).hom.app (restrict X A F W)

/-- The cartesian restriction map over an identity agrees with the chosen identity comparison. -/
@[stacks 08PE "cartesian restriction identity law"]
theorem cartesianRestriction_id
    (F : X.totalᵒᵖ ⥤ A) (U : C) :
    cartesianRestriction X A F (𝟙 U) = cartesianRestrictionId X A F U := sorry

/-- The cartesian restriction map over a composite agrees with the composite comparison. -/
@[stacks 08PE "cartesian restriction composition law"]
theorem cartesianRestriction_comp
    (F : X.totalᵒᵖ ⥤ A) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    cartesianRestriction X A F (g ≫ f) = cartesianRestrictionComp X A F f g := sorry

@[simp]
theorem cartesianRestriction_app
    (F : X.totalᵒᵖ ⥤ A) {U V : C} (f : V ⟶ U)
    (x : (X.p.Fiber U)ᵒᵖ) :
    (cartesianRestriction X A F f).app x = cartesianRestrictionApp X A F f x := sorry

end CategoryTheory.FiberedCategoryOver.Presheaf
