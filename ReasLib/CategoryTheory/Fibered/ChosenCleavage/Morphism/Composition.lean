/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex

/-!
# Composition coherence for selected reindexing comparisons

This module records compatibility of selected-cleavage comparison isomorphisms
with composition of morphisms of fibred categories and with specified
composition in the base category.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

-- Use cartesian uniqueness directly: the general comparison coherence API is still deferred.
private theorem composition_ext {S : Type uS} [Category.{vS} S] {p : S ⥤ C}
    {U V : C} {x y : p.Fiber V} {z : S} {cart : y.1 ⟶ z} {f : V ⟶ U}
    (hcart : p.IsStronglyCartesian f cart) (φ ψ : x ⟶ y)
    (h : φ.1 ≫ cart = ψ.1 ≫ cart) : φ = ψ := by
  apply Fiber.hom_ext
  exact @IsStronglyCartesian.ext C S _ _ p V U y.1 z f cart hcart V x.1
    (𝟙 V) φ.1 ψ.1 φ.2 ψ.2 h

@[reassoc]
private theorem composition_map_fac (F : X ⟶ Y) {U V : C}
    (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso F f x).hom.1 ≫
        (toFunctor F).map (Functor.Chosen.cartesianHom X.p f x) =
      Functor.Chosen.cartesianHom Y.p f ((fiberFunctor F U).obj x) := by
  have hcart : Y.p.IsStronglyCartesian f
      ((toFunctor F).map (Functor.Chosen.cartesianHom X.p f x)) :=
    CartesianBasedFunctor.Map.stronglyCartesianOfLift (toCartesianBasedFunctor F) f _
      ((Functor.Cleavage.ofIsFibered X.p).reindexLift f x).isStronglyCartesian
  have hlift : Y.p.IsHomLift f
      (Functor.Chosen.cartesianHom Y.p f ((fiberFunctor F U).obj x)) :=
    ((Functor.Cleavage.ofIsFibered Y.p).reindexLift f
      ((fiberFunctor F U).obj x)).isStronglyCartesian.toIsHomLift
  exact @IsStronglyCartesian.fac C Y.total _ _ Y.p V U _ _ f _ hcart V _
    (𝟙 V) f (Category.id_comp f).symm _ hlift

@[reassoc]
private theorem composition_reindex_fac {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : p.Fiber U} (φ : x ⟶ y) :
    (Functor.Chosen.reindexMap p f φ).1 ≫ Functor.Chosen.cartesianHom p f y =
      Functor.Chosen.cartesianHom p f x ≫ φ.1 := by
  let χ := Functor.Cleavage.ofIsFibered p
  have hcart : p.IsStronglyCartesian f (χ.cartesianHom f y) :=
    (χ.reindexLift f y).isStronglyCartesian
  have hlift : p.IsHomLift f (χ.cartesianHom f x ≫ φ.1) :=
    @IsHomLift.comp_lift_id_right' C S _ _ p V U
      (χ.reindexObj f x).1 x.1 y.1 f (χ.cartesianHom f x)
      (χ.reindexLift f x).isStronglyCartesian.toIsHomLift U φ.1 φ.2
  exact @IsStronglyCartesian.fac C S _ _ p V U _ _ f _ hcart V _
    (𝟙 V) f (Category.id_comp f).symm _ hlift

@[reassoc]
private theorem composition_specified_fac {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) [p.IsFibered] {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : p.Fiber U) :
    (Functor.Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).hom.1 ≫
        Functor.Chosen.cartesianHom p g (Functor.Chosen.reindexObj p f x) ≫
        Functor.Chosen.cartesianHom p f x =
      Functor.Chosen.cartesianHom p gf x := by
  subst gf
  let χ := Functor.Cleavage.ofIsFibered p
  letI : p.IsStronglyCartesian f (χ.cartesianHom f x) :=
    (χ.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian g (χ.cartesianHom g (χ.reindexObj f x)) :=
    (χ.reindexLift g (χ.reindexObj f x)).isStronglyCartesian
  letI : p.IsHomLift (g ≫ f) (χ.cartesianHom (g ≫ f) x) :=
    (χ.reindexLift (g ≫ f) x).isStronglyCartesian.toIsHomLift
  change (𝟙 _ ≫ (Functor.Cleavage.Reindex.compIsoApp χ f g x).hom).1 ≫ _ ≫ _ = _
  rw [Category.id_comp]
  dsimp only [Functor.Cleavage.Reindex.compIsoApp, Functor.Cleavage.Reindex.compAmbientIso,
    IsStronglyCartesian.DomainIso.ofBaseIso, IsStronglyCartesian.domainIsoOfBaseIso]
  apply IsStronglyCartesian.fac

/-- The selected-cleavage comparison for a composite owner morphism is the composite of the
individual comparison isomorphisms. -/
theorem Reindex.mapIso.comp {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    Reindex.mapIso (F ≫ G) f x =
      Reindex.mapIso G f ((fiberFunctor F U).obj x) ≪≫
        (fiberFunctor G V).mapIso (Reindex.mapIso F f x) := by
  apply Iso.ext
  apply composition_ext
    (CartesianBasedFunctor.Map.stronglyCartesianOfLift
      (toCartesianBasedFunctor (F ≫ G)) f _
      ((Functor.Cleavage.ofIsFibered X.p).reindexLift f x).isStronglyCartesian)
  change (Reindex.mapIso (F ≫ G) f x).hom.1 ≫
      (toFunctor (F ≫ G)).map (Functor.Chosen.cartesianHom X.p f x) =
    ((Reindex.mapIso G f ((fiberFunctor F U).obj x)).hom.1 ≫
      (toFunctor G).map (Reindex.mapIso F f x).hom.1) ≫
        (toFunctor G).map ((toFunctor F).map (Functor.Chosen.cartesianHom X.p f x))
  rw [composition_map_fac, Category.assoc]
  erw [← Functor.map_comp,
    composition_map_fac, composition_map_fac]
  rfl

/-- The forward comparison for a composite owner morphism is the composite of the two forward
comparison maps. -/
theorem Reindex.mapIso.comp.hom {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso (F ≫ G) f x).hom =
      (Reindex.mapIso G f ((fiberFunctor F U).obj x)).hom ≫
        (fiberFunctor G V).map (Reindex.mapIso F f x).hom := by
  exact congrArg Iso.hom (Reindex.mapIso.comp F G f x)

/-- The inverse comparison for a composite owner morphism is the reverse composite of the two
inverse comparison maps. -/
theorem Reindex.mapIso.comp.inv {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso (F ≫ G) f x).inv =
      (fiberFunctor G V).map (Reindex.mapIso F f x).inv ≫
        (Reindex.mapIso G f ((fiberFunctor F U).obj x)).inv := by
  exact congrArg Iso.inv (Reindex.mapIso.comp F G f x)

/-- Total-category readout of `Reindex.mapIso.comp.hom`. -/
theorem Reindex.mapIso.comp.totalHom
    {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso (F ≫ G) f x).hom.1 =
      (Reindex.mapIso G f ((fiberFunctor F U).obj x)).hom.1 ≫
        ((fiberFunctor G V).map (Reindex.mapIso F f x).hom).1 := by
  exact congrArg Subtype.val (Reindex.mapIso.comp.hom F G f x)

/-- Total-category readout of `Reindex.mapIso.comp.inv`. -/
theorem Reindex.mapIso.comp.totalInv
    {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    (Reindex.mapIso (F ≫ G) f x).inv.1 =
      ((fiberFunctor G V).map (Reindex.mapIso F f x).inv).1 ≫
        (Reindex.mapIso G f ((fiberFunctor F U).obj x)).inv.1 := by
  exact congrArg Subtype.val (Reindex.mapIso.comp.inv F G f x)

/-- The selected-cleavage comparison is compatible with a specified composite of base arrows. -/
theorem Reindex.mapIso.specifiedComp.hom (F : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x)).hom ≫
        Functor.Chosen.reindexMap Y.p g (Reindex.mapIso F f x).hom ≫
        (Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).hom =
      (Reindex.mapIso F gf x).hom ≫
        (fiberFunctor F W).map
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).hom := by
  have hcart : X.p.IsStronglyCartesian gf
      (Functor.Chosen.cartesianHom X.p g (Functor.Chosen.reindexObj X.p f x) ≫
        Functor.Chosen.cartesianHom X.p f x) := by
    subst gf
    exact @IsStronglyCartesian.comp C X.total _ _ X.p W V U
      (Functor.Chosen.reindexObj X.p g (Functor.Chosen.reindexObj X.p f x)).1
      (Functor.Chosen.reindexObj X.p f x).1 x.1 g f _ _
      ((Functor.Cleavage.ofIsFibered X.p).reindexLift g
        (Functor.Chosen.reindexObj X.p f x)).isStronglyCartesian
      ((Functor.Cleavage.ofIsFibered X.p).reindexLift f x).isStronglyCartesian
  apply composition_ext
    (CartesianBasedFunctor.Map.stronglyCartesianOfLift
      (toCartesianBasedFunctor F) gf _ hcart)
  change
    ((Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
        ((fiberFunctor F U).obj x)).hom.1 ≫
      (Functor.Chosen.reindexMap Y.p g (Reindex.mapIso F f x).hom).1 ≫
      (Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).hom.1) ≫
        (toFunctor F).map
          (Functor.Chosen.cartesianHom X.p g (Functor.Chosen.reindexObj X.p f x) ≫
            Functor.Chosen.cartesianHom X.p f x) =
      ((Reindex.mapIso F gf x).hom.1 ≫
        (toFunctor F).map
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).hom.1) ≫
        (toFunctor F).map
          (Functor.Chosen.cartesianHom X.p g (Functor.Chosen.reindexObj X.p f x) ≫
            Functor.Chosen.cartesianHom X.p f x)
  have hsource := congrArg (toFunctor F).map (composition_specified_fac X.p f g gf hgf x)
  simp only [Functor.map_comp] at hsource
  simp only [Functor.map_comp, Category.assoc]
  erw [composition_map_fac_assoc F g (Functor.Chosen.reindexObj X.p f x),
    composition_reindex_fac_assoc Y.p g (Reindex.mapIso F f x).hom,
    composition_map_fac F f x,
    composition_specified_fac Y.p f g gf hgf ((fiberFunctor F U).obj x),
    hsource, composition_map_fac F gf x]

/-- Cancellation form of selected-cleavage composition coherence. -/
theorem Reindex.mapIso.specifiedComp.boundary (F : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x)).hom ≫
        Functor.Chosen.reindexMap Y.p g (Reindex.mapIso F f x).hom =
      (Reindex.mapIso F gf x).hom ≫
        (fiberFunctor F W).map
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).hom ≫
        (Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).inv := by
  exact ((Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).eq_comp_inv.mpr
    ((Category.assoc _ _ _).trans
      (Reindex.mapIso.specifiedComp.hom F f g gf hgf x))).trans (Category.assoc _ _ _)

/-- Inverse form of selected-cleavage composition coherence. -/
theorem Reindex.mapIso.specifiedComp.inv (F : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).inv ≫
        Functor.Chosen.reindexMap Y.p g (Reindex.mapIso F f x).inv ≫
        (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x)).inv =
      (fiberFunctor F W).map
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).inv ≫
        (Reindex.mapIso F gf x).inv := by
  have h :
      (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x) ≪≫
        (Functor.Chosen.reindex Y.p g).mapIso (Reindex.mapIso F f x) ≪≫
        Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)) =
      Reindex.mapIso F gf x ≪≫
        (fiberFunctor F W).mapIso
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x) :=
    Iso.ext (Reindex.mapIso.specifiedComp.hom F f g gf hgf x)
  exact (Category.assoc _ _ _).symm.trans (congrArg Iso.inv h)

/-- The selected reindexing comparison is compatible with a specified composite as an equality
of fiber isomorphisms.

This packages `Reindex.mapIso.specifiedComp.hom` as an equality of the canonical selected-cleavage
comparison isomorphisms. -/
theorem Reindex.mapIso.specifiedComp.cocycle
    (F : X ⟶ Y) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) {gf : W ⟶ U}
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
        ((fiberFunctor F U).obj x) ≪≫
      ((Functor.fiberPseudofunctor Y.p).map g.op.toLoc).toFunctor.mapIso
        (Reindex.mapIso F f x) ≪≫
        Reindex.mapIso F g
          (f⁎[X.chosenCleavage] x)) =
      Reindex.mapIso F gf x ≪≫
        (fiberFunctor F W).mapIso
          (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x) := by
  apply Iso.ext
  exact Reindex.mapIso.specifiedComp.hom F f g gf hgf x

/-- The inverse comparison over a composite, the target composition comparison, and the
selected cartesian arrow over the second factor reduce to the image of the corresponding
source composite after the forward comparison over the first factor.

This is the total-category normalization of selected reindexing composition coherence. -/
theorem Reindex.mapIso.specifiedComp.invCartesian (F : X ⟶ Y)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (hgf : g ≫ f = gf) (x : X.p.Fiber U) :
    (Reindex.mapIso F gf x).inv.1 ≫
        (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
          ((fiberFunctor F U).obj x)).hom.1 ≫
        Functor.Chosen.cartesianHom Y.p g
          (Functor.Chosen.reindexObj Y.p f ((fiberFunctor F U).obj x)) ≫
        (Reindex.mapIso F f x).hom.1 =
      (toFunctor F).map
        ((Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).hom.1 ≫
          Functor.Chosen.cartesianHom X.p g
            (Functor.Chosen.reindexObj X.p f x)) := by
  have h := (Reindex.mapIso F gf x).inv_comp_eq.mpr
    (Reindex.mapIso.specifiedComp.hom F f g gf hgf x)
  have ht := congrArg (fun k => k.1 ≫ (toFunctor F).map
    (Functor.Chosen.cartesianHom X.p g (Functor.Chosen.reindexObj X.p f x))) h
  change
    (((Reindex.mapIso F gf x).inv.1 ≫
      (Functor.Chosen.Reindex.specifiedCompIsoApp Y.p f g gf hgf
        ((fiberFunctor F U).obj x)).hom.1 ≫
      (Functor.Chosen.reindexMap Y.p g (Reindex.mapIso F f x).hom).1 ≫
      (Reindex.mapIso F g (Functor.Chosen.reindexObj X.p f x)).hom.1) ≫
      (toFunctor F).map
        (Functor.Chosen.cartesianHom X.p g (Functor.Chosen.reindexObj X.p f x))) =
      (toFunctor F).map
        (Functor.Chosen.Reindex.specifiedCompIsoApp X.p f g gf hgf x).hom.1 ≫
      (toFunctor F).map
        (Functor.Chosen.cartesianHom X.p g (Functor.Chosen.reindexObj X.p f x)) at ht
  let t := (toFunctor F).map
    (Functor.Chosen.cartesianHom X.p g (Functor.Chosen.reindexObj X.p f x))
  erw [Category.assoc _ _ t, Category.assoc _ _ t, Category.assoc _ _ t,
    composition_map_fac F g (Functor.Chosen.reindexObj X.p f x),
    composition_reindex_fac Y.p g (Reindex.mapIso F f x).hom,
    ← Functor.map_comp] at ht
  exact ht

end FiberedCategoryOver

end CategoryTheory
